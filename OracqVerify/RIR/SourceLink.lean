module

public import OracqVerify.RIR.Link

/-! Translation validation of an external binder on decoded RIR programs. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Matrix
open scoped Matrix

/-- An approved bank layout can permute the original formals and introduce captures. -/
inductive BankActual where
  | original (index : Nat)
  | captured (bank : Resource)

abbrev CapturePlan := List (String × List BankActual)

private def BankActual.originalIndex : BankActual → Option Nat
  | .original index => some index
  | .captured _ => none

private def bankActuals (plan : CapturePlan) (name : String) (original : List Resource) :
    Except String (List Resource) := do
  let some layout := plan.lookup name | return original
  let forwarded := layout.filterMap BankActual.originalIndex
  unless forwarded.length = original.length ∧ forwarded.Nodup do
    throw s!"Capture plan must forward every original bank exactly once at {name}"
  layout.mapM fun
    | .original index =>
      match original[index]? with
      | some bank => .ok bank
      | none => .error s!"Capture plan references missing original bank {index} at {name}"
    | .captured bank => .ok bank

def ResolvedInstruction.withCaptures (plan : CapturePlan) :
    ResolvedInstruction → Except String ResolvedInstruction
  | .query name wires banks => return .query name wires (← bankActuals plan name banks)
  | .controlled guard body => return .controlled guard (← body.withCaptures plan)
  | .adjoint body => return .adjoint (← body.withCaptures plan)
  | atom => .ok atom

/-- The caller declares capture choices independently of the proposed bound artifact. -/
def ResolvedProgram.withCaptures (program : ResolvedProgram) (plan : CapturePlan) :
    Except String ResolvedProgram := do
  let instructions ← program.instructions.mapM (ResolvedInstruction.withCaptures plan)
  return { program with instructions }

private def callSite : ResolvedInstruction → Option CallSite
  | .query name wires banks => some ⟨name, wires, banks⟩
  | .controlled _ body | .adjoint body => callSite body
  | _ => none

abbrev PlacedImplementations := List (CallSite × List ResolvedInstruction)

def PlacedImplementations.atSite (placed : PlacedImplementations) : Implementations := fun site =>
  ((placed.find? (fun pair => decide (pair.1 = site))).map Prod.snd).getD []

/-- Place an implementation in the actual coordinates of a resolved call. The enclosing
control and adjoint are applied by inlining, so placement starts with an empty context. -/
private def placeImplementation (source bound : Program) (site : CallSite) :
    Except String (CallSite × List ResolvedInstruction) := do
  let declaration ← lookupModule source site.name
  let m ← lookupModule bound site.name
  unless m.body.isSome do throw s!"Unbound slot {site.name}"
  unless m.registers.map Register.type = declaration.registers.map Register.type do
    throw s!"Binding changed the quantum interface at {site.name}"
  let frame : Frame := ⟨(m.registers.map Register.name).zip site.arguments,
    (m.resources.map Resource.name).zip site.banks⟩
  let word ← resolveModule bound bound.modules.length m frame {}
  if word.any (fun step => (callSite step).isSome) then
    throw s!"Implementation at {site.name} still calls an open slot"
  return (site, word)

def ResolvedProgram.inline (program : ResolvedProgram) (placed : Implementations) : ResolvedProgram :=
  { program with instructions := program.instructions.flatMap (ResolvedInstruction.inline placed) }

/-- Push an adjoint through controls and cancel an adjacent adjoint. -/
private def adjointNormal : ResolvedInstruction → ResolvedInstruction
  | .controlled guard body => .controlled guard (adjointNormal body)
  | .adjoint body => body
  | atom => .adjoint atom

def ResolvedInstruction.normalize : ResolvedInstruction → ResolvedInstruction
  | .controlled guard body => .controlled guard body.normalize
  | .adjoint body => adjointNormal body.normalize
  | atom => atom

private theorem ResolvedInstruction.adjointNormal_matrix (width : Nat) (snapshot : Snapshot)
    (step : ResolvedInstruction) :
    (adjointNormal step).matrix width snapshot =
      (ResolvedInstruction.adjoint step).matrix width snapshot := by
  induction step with
  | controlled guard body ih =>
    simp only [adjointNormal, matrix, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases View.ofWires width guard.wires.length guard.wires <;>
      cases body.matrix width snapshot <;> simp [controlledMatrix_adjoint]
  | adjoint body =>
    cases h : body.matrix width snapshot <;> simp [adjointNormal, matrix, h, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
  | unary _ _ | gphase _ | xor _ _ | addConst _ _ | load _ _ _ | query _ _ _ => rfl

private theorem ResolvedInstruction.normalize_matrix (width : Nat) (snapshot : Snapshot)
    (step : ResolvedInstruction) : step.normalize.matrix width snapshot = step.matrix width snapshot := by
  induction step with
  | controlled _ _ ih => simp only [normalize, matrix, ih]
  | adjoint _ ih => simp only [normalize, adjointNormal_matrix, matrix, ih]
  | unary _ _ | gphase _ | xor _ _ | addConst _ _ | load _ _ _ | query _ _ _ => rfl

private theorem adjointNormal_matrixWith (width : Nat) (snapshot : Snapshot) (oracle : Oracle width)
    (step : ResolvedInstruction) :
    (adjointNormal step).matrixWith width snapshot oracle =
      (ResolvedInstruction.adjoint step).matrixWith width snapshot oracle := by
  induction step with
  | controlled guard body ih =>
    simp only [adjointNormal, ResolvedInstruction.matrixWith, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases View.ofWires width guard.wires.length guard.wires <;>
      cases body.matrixWith width snapshot oracle <;> simp [controlledMatrix_adjoint]
  | adjoint body =>
    cases h : body.matrixWith width snapshot oracle <;> simp [adjointNormal,
      ResolvedInstruction.matrixWith, h, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | unary _ _ | gphase _ | xor _ _ | addConst _ _ | load _ _ _ | query _ _ _ => rfl

theorem ResolvedInstruction.normalize_matrixWith (width : Nat) (snapshot : Snapshot) (oracle : Oracle width)
    (step : ResolvedInstruction) :
    step.normalize.matrixWith width snapshot oracle = step.matrixWith width snapshot oracle := by
  induction step with
  | controlled _ _ ih => simp only [normalize, matrixWith, ih]
  | adjoint _ ih => simp only [normalize, adjointNormal_matrixWith, matrixWith, ih]
  | unary _ _ | gphase _ | xor _ _ | addConst _ _ | load _ _ _ | query _ _ _ => rfl

/-- Canonicalize the placement of adjoints inside the resolved instruction wrappers. -/
@[expose] def ResolvedProgram.normalize (program : ResolvedProgram) : ResolvedProgram :=
  { program with instructions := program.instructions.map ResolvedInstruction.normalize }

theorem ResolvedProgram.normalize_matrix (program : ResolvedProgram) (snapshot : Snapshot) :
    program.normalize.matrix snapshot = program.matrix snapshot := by
  simp [normalize, matrix, Function.comp_def, ResolvedInstruction.normalize_matrix]; rfl

/-- Interpret a resolved caller in an environment for the effective (capture-aware) call sites. -/
noncomputable def ResolvedProgram.matrixWith (program : ResolvedProgram) (snapshot : Snapshot)
    (oracle : Oracle program.wireCount) : Except String (WireMatrix program.wireCount) := do
  let gates ← program.instructions.mapM (ResolvedInstruction.matrixWith program.wireCount snapshot oracle)
  return wordMatrix gates

/-- Structural evidence relating two decoded artifacts, independent of oracle correctness. -/
structure SourceLink (source bound : Program) (plan : CapturePlan) where
  sourceTrace : ResolvedProgram
  boundary : ResolvedProgram
  closed : ResolvedProgram
  placed : PlacedImplementations
  source_resolved : source.resolve = .ok sourceTrace
  captured : sourceTrace.withCaptures plan = .ok boundary
  bound_resolved : bound.resolve = .ok closed
  inlined : closed.normalize = (boundary.inline placed.atSite).normalize

/-- Check the bound caller with its former oracle bodies hidden, then independently check
the full bound resolution against the result of contextual inlining. -/
def verifySourceLink (source bound : Program) (plan : CapturePlan := []) :
    Except String (SourceLink source bound plan) := do
  unless source.entry = bound.entry do throw "Binding changed the entry name"
  let srcEntry ← lookupModule source source.entry
  let boundEntry ← lookupModule bound bound.entry
  unless srcEntry.registers = boundEntry.registers ∧
      (∀ bank ∈ srcEntry.resources, bank ∈ boundEntry.resources) do
    throw "Binding changed the original entry interface"
  let slots := (source.modules.filter (fun m => m.body.isNone)).map Module.name
  unless (plan.map Prod.fst).Nodup ∧ (∀ key ∈ plan.map Prod.fst, key ∈ slots) do
    throw "Capture plan must name distinct open slots"
  match hSource : source.resolve with
  | .error reason => throw reason
  | .ok trace =>
    match hCapture : trace.withCaptures plan with
    | .error reason => throw reason
    | .ok boundary =>
      let cutModules := bound.modules.map fun m =>
        if slots.contains m.name then { m with body := none } else m
      let cutTrace ← ({ bound with modules := cutModules }).resolve
      unless cutTrace = boundary do
        throw "Binding changed the caller or its ordered wire or bank actuals"
      let sites := (boundary.instructions.filterMap callSite).eraseDupsBy
        (fun x y => decide (x = y))
      let placed ← sites.mapM (placeImplementation source bound)
      match hBound : bound.resolve with
      | .error reason => throw reason
      | .ok closed =>
        if hInline : closed.normalize = (boundary.inline (PlacedImplementations.atSite placed)).normalize then
          return ⟨trace, boundary, closed, placed, hSource, hCapture, hBound, hInline⟩
        else throw "Bound trace differs from contextual inlining of the placed implementations"

/-- A checked artifact pair reduces matrix correctness to contracts at its actual call sites.
The source resolution and capture equations in the certificate identify the abstract caller. -/
theorem SourceLink.sound {source bound : Program} {plan : CapturePlan}
    (link : SourceLink source bound plan) (snapshot : Snapshot)
    (oracle : Oracle link.boundary.wireCount)
    (checked : ∀ step ∈ link.boundary.instructions, ∃ word,
      LinkStep link.boundary.wireCount snapshot oracle link.placed.atSite step word) :
    bound.matrix snapshot = (do
      let matrix ← link.boundary.matrixWith snapshot oracle
      pure ⟨link.boundary.wireCount, matrix⟩) := by
  have same : (link.boundary.inline link.placed.atSite).matrix snapshot =
      link.boundary.matrixWith snapshot oracle := linkWord_sound _ checked
  have normalized (program : ResolvedProgram) :
      (do let matrix ← program.normalize.matrix snapshot
          pure (⟨program.normalize.wireCount, matrix⟩ : Σ n : Nat, WireMatrix n)) =
      (do let matrix ← program.matrix snapshot
          pure (⟨program.wireCount, matrix⟩ : Σ n : Nat, WireMatrix n)) := by
    change (do let matrix ← program.normalize.matrix snapshot
               pure (⟨program.wireCount, matrix⟩ : Σ n : Nat, WireMatrix n)) = _
    rw [program.normalize_matrix snapshot]; rfl
  unfold Program.matrix
  rw [link.bound_resolved]
  change (do let matrix ← link.closed.matrix snapshot
             pure (⟨link.closed.wireCount, matrix⟩ : Σ n : Nat, WireMatrix n)) = _
  rw [← normalized link.closed, link.inlined, normalized, same]; rfl

end OracqVerify.RIR
