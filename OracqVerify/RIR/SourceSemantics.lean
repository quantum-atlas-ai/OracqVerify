module

public import OracqVerify.RIR.ScopedSourceLink

/-! Independent interpretation of named RIR bodies, with validation against scoped resolution. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR.SourceSemantics

/-- Elaborate a named instruction without accumulating or distributing context. Controls and
adjoints with a single operand retain their source nesting. Calls retain their ordered views. -/
def instruction (program : Program) (frame : Frame) :
    Nat → Instruction → Except String ResolvedInstruction
  | 0, _ => .error "Source operand is nested too deeply"
  | _ + 1, .unary gate target => return .unary gate (← resolveRef frame target)
  | _ + 1, .phase angle target => do
    let [wire] ← resolveRef frame target | throw "Source phase requires a one-wire view"
    return .controlled ⟨[wire], 1⟩ (.gphase angle)
  | _ + 1, .gphase angle => .ok (.gphase angle)
  | _ + 1, .xor source target => return .xor (← resolveRef frame source) (← resolveRef frame target)
  | _ + 1, .addConst target amount => return .addConst (← resolveRef frame target) amount
  | _ + 1, .load resource address data => do
    return .load (← lookup frame.resources resource "source bank")
      (← resolveRef frame address) (← resolveRef frame data)
  | _ + 1, .call name arguments banks => do
    let callee ← lookupModule program name
    let placed ← resolveCall frame callee arguments banks
    return .query name (placed.registers.map Prod.snd) (placed.resources.map Prod.snd)
  | fuel + 1, .control guard value [body] => do
    return .controlled ⟨← resolveRef frame guard, value⟩ (← instruction program frame fuel body)
  | fuel + 1, .adjoint [body] => return .adjoint (← instruction program frame fuel body)
  | _ + 1, _ => .error "Source check supports singleton controls and adjoints and primitive sequences"

def definition (program : Program) (node : ScopedModule) : Except String ScopedModule := do
  let source ← lookupModule program node.name
  let frame := ⟨rootRegisters (source.registers ++ source.locals) 0,
    source.resources.map fun bank => (bank.name, bank)⟩
  let body ← source.body.mapM (List.mapM (instruction program frame 128))
  let publicWires := source.registers.foldl (fun count r => count + r.type.width) 0
  let localWires := source.locals.foldl (fun count r => count + r.type.width) 0
  return { node with publicWires, localWires, banks := source.resources, body }

def namedGraph (program : Program) (order : ScopedProgram) : Except String ScopedProgram := do
  return { order with entry := program.entry, modules := ← order.modules.mapM (definition program) }

def normalizeModule (node : ScopedModule) : ScopedModule :=
  { node with body := node.body.map (List.map ResolvedInstruction.normalize) }

def normalize (graph : ScopedProgram) : ScopedProgram :=
  { graph with modules := graph.modules.map normalizeModule }

private theorem mapM_normalize (width : Nat) (memory : Snapshot) (oracle : Oracle width)
    (steps : List ResolvedInstruction) :
    (steps.map ResolvedInstruction.normalize).mapM (ResolvedInstruction.matrixWith width memory oracle) =
      steps.mapM (ResolvedInstruction.matrixWith width memory oracle) := by
  simp [List.mapM_map, Function.comp_def, ResolvedInstruction.normalize_matrixWith]

private theorem normalize_interpret (node : ScopedModule) (known : ScopedEnvironment) :
    (normalizeModule node).interpret known = node.interpret known := by
  cases node with
  | mk name publicWires localWires banks code peak controls adjoints =>
    funext memory
    cases code with
    | none => rfl
    | some steps =>
      simp only [normalizeModule, Option.map_some, ScopedModule.interpret, ScopedModule.bodyMatrix,
        ScopedModule.width, ScopedModule.Clean, ScopedModule.publicMatrix]
      have h := mapM_normalize (publicWires + localWires) memory
        (known.atCall (publicWires + localWires) memory) steps
      simp only [h, ScopedModule.frame]
      rfl

private theorem normalize_environment (slots : List String) (oracle : ScopedOracle)
    (nodes : List ScopedModule) (initial : ScopedEnvironment) :
    scopedEnvironment (nodes.map normalizeModule) slots oracle initial =
      scopedEnvironment nodes slots oracle initial := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons node rest ih =>
    have head : initial.extend (normalizeModule node) slots oracle = initial.extend node slots oracle := by
      unfold ScopedEnvironment.extend
      rw [show (normalizeModule node).name = node.name from rfl]
      split
      · rfl
      · rw [normalize_interpret]
        rfl
    simp only [scopedEnvironment, List.map_cons, List.foldl_cons, head]
    exact ih _

theorem normalize_matrix (graph : ScopedProgram) (memory : Snapshot)
    (slots : List String) (oracle : ScopedOracle) :
    (normalize graph).matrixWith memory slots oracle = graph.matrixWith memory slots oracle := by
  simp only [ScopedProgram.matrixWith, normalize, normalize_environment]
  rfl

structure Certificate (program : Program) where
  resolved : ScopedProgram
  source : ScopedProgram
  resolution : program.resolveScoped = .ok resolved
  elaboration : namedGraph program resolved = .ok source
  agreement : normalize source = normalize resolved

def certify (program : Program) : Except String (Certificate program) := do
  match resolution : program.resolveScoped with
  | .error reason => throw reason
  | .ok resolved =>
    match elaboration : namedGraph program resolved with
    | .error reason => throw reason
    | .ok source =>
      if agreement : normalize source = normalize resolved then
        return ⟨resolved, source, resolution, elaboration, agreement⟩
      else throw "Named source and scoped resolution disagree"

/-- Evaluation of the source body nesting, in the checked dependency order. -/
noncomputable def evaluate (program : Program) (order : ScopedProgram)
    (memory : Snapshot) (slots : List String) (oracle : ScopedOracle) :
    Except String (Σ width : Nat, WireMatrix width) := do
  let source ← namedGraph program order
  return ⟨source.entryWires, ← source.matrixWith memory slots oracle⟩

/-- A checked named program and its scoped resolution agree on arbitrary snapshots and oracles. -/
theorem Certificate.sound {program : Program} (cert : Certificate program)
    (memory : Snapshot) (slots : List String) (oracle : ScopedOracle) :
    evaluate program cert.resolved memory slots oracle = (do
      let matrix ← cert.resolved.matrixWith memory slots oracle
      pure ⟨cert.resolved.entryWires, matrix⟩) := by
  have execution (graph : ScopedProgram) :
      (do let matrix ← (normalize graph).matrixWith memory slots oracle
          pure (⟨(normalize graph).entryWires, matrix⟩ : Σ width, WireMatrix width)) =
      (do let matrix ← graph.matrixWith memory slots oracle
          pure (⟨graph.entryWires, matrix⟩ : Σ width, WireMatrix width)) := by
    change (do let matrix ← (normalize graph).matrixWith memory slots oracle
               pure (⟨graph.entryWires, matrix⟩ : Σ width, WireMatrix width)) = _
    rw [normalize_matrix]
    rfl
  unfold evaluate
  rw [cert.elaboration]
  simp only [Bind.bind, Except.bind]
  change (do let matrix ← cert.source.matrixWith memory slots oracle
             pure (⟨cert.source.entryWires, matrix⟩ : Σ width, WireMatrix width)) = _
  rw [← execution cert.source, cert.agreement, execution]
  rfl

end OracqVerify.RIR.SourceSemantics
