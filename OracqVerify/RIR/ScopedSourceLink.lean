module

public import OracqVerify.RIR.ScopedLink
public import OracqVerify.RIR.SourceLink

/-! Translation validation of an external binder across lexical scope boundaries. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

/-- For each caller, record the approved bank layout of its direct callees.
Captured bank names are expressed in the caller's lexical frame. -/
abbrev ScopedCapturePlan := List (String × CapturePlan)

private def callSite : ResolvedInstruction → Option CallSite
  | .query name args banks => some ⟨name, args, banks⟩
  | .controlled _ step | .adjoint step => callSite step
  | _ => none

@[expose] def scopedSlots (program : ScopedProgram) : List String :=
  (program.modules.filter fun m => m.body.isNone).map ScopedModule.name

private def scopedLookup (program : ScopedProgram) (name : String) :
    Except String ScopedModule :=
  match program.modules.find? (fun m => m.name == name) with
  | some m => .ok m
  | none => .error s!"Missing scoped module {name}"

private def checkCalleeBanks (caller closed : ScopedProgram) (layouts : CapturePlan)
    (name : String) : Except String Unit := do
  let original ← scopedLookup caller name
  let candidate ← scopedLookup closed name
  -- A slot's contract is stated in the implementation's bank frame. A retained
  -- callee continues to interpret each original bank by its old lexical name.
  if original.body.isNone then return ()
  let some layout := layouts.lookup name |
    unless original.banks = candidate.banks do
      throw s!"Binding changed the ordered bank interface of {name}"
    return ()
  unless layout.length = candidate.banks.length do
    throw s!"Capture layout does not match the bank interface of {name}"
  for (actual, formal) in layout.zip candidate.banks do
    match actual with
    | .original index =>
      unless original.banks[index]? = some formal do
        throw s!"Capture layout changed an original bank of {name}"
    | .captured _ =>
      if original.banks.contains formal then
        throw s!"Capture layout overwrote an original bank of {name}"

private def restoreCaller (source bound : Program) (caller closed : ScopedProgram)
    (plan : ScopedCapturePlan) (original : ScopedModule) : Except String (String × ScopedModule) := do
  let candidate ← scopedLookup closed original.name
  let srcModule ← lookupModule source original.name
  let boundModule ← lookupModule bound original.name
  unless srcModule.registers.map Register.type = boundModule.registers.map Register.type do
    throw s!"Binding changed the quantum interface of {original.name}"
  let some body := original.body |
    if original.name = source.entry ∧ original.banks ≠ candidate.banks then
      throw "Binding an open entry changed its bank interface"
    else return (original.name, { candidate with body := none })
  unless srcModule.locals.map Register.type = boundModule.locals.map Register.type do
    throw s!"Binding changed the caller workspace of {original.name}"
  let layouts := (plan.lookup original.name).getD []
  let calls := (body.filterMap callSite).map CallSite.name
  unless (layouts.map Prod.fst).Nodup ∧ (∀ callee ∈ layouts.map Prod.fst, callee ∈ calls) do
    throw s!"Scoped capture plan must name distinct direct callees of {original.name}"
  calls.eraseDups.forM (checkCalleeBanks caller closed layouts)
  let expected ← body.mapM (ResolvedInstruction.withCaptures layouts)
  let captured := ((expected.filterMap callSite).flatMap CallSite.banks).eraseDups.filter (fun bank =>
    !original.banks.contains bank)
  unless (∀ bank ∈ original.banks, bank ∈ candidate.banks) ∧
      (∀ bank ∈ candidate.banks, bank ∈ original.banks ∨ bank ∈ captured) do
    throw s!"Binding changed the original banks or introduced an unapproved bank in {original.name}"
  return (original.name, { candidate with body := some expected })

/-- Check each retained caller in its relative frame and require a closed
implementation graph. Slot bodies and their private helpers remain opaque. -/
def checkScopedBoundary (source bound : Program) (caller closed : ScopedProgram)
    (plan : ScopedCapturePlan) : Except String ScopedProgram := do
  unless source.entry = bound.entry do throw "Binding changed the entry name"
  unless caller.entryWires = closed.entryWires do throw "Binding changed the entry width"
  unless (plan.map Prod.fst).Nodup ∧
      (∀ name ∈ plan.map Prod.fst, caller.modules.any (fun m => m.name == name && m.body.isSome)) do
    throw "Scoped capture plan must name distinct retained caller definitions"
  unless closed.modules.all (fun m => m.body.isSome) do
    throw "Bound artifact still has an open scoped slot"
  let retained ← caller.modules.mapM (restoreCaller source bound caller closed plan)
  return { closed with modules := closed.modules.map fun m => (retained.lookup m.name).getD m }

/-- Structural evidence relating the two independently decoded scoped artifacts. -/
structure ScopedSourceLink (source bound : Program) (plan : ScopedCapturePlan) where
  caller : ScopedProgram
  closed : ScopedProgram
  exposed : ScopedProgram
  source_resolved : source.resolveScoped = .ok caller
  bound_resolved : bound.resolveScoped = .ok closed
  rebuilt : checkScopedBoundary source bound caller closed plan = .ok exposed
  checked : exposed = closed.hideSlots (scopedSlots caller)

def verifyScopedSourceLink (source bound : Program) (plan : ScopedCapturePlan := []) :
    Except String (ScopedSourceLink source bound plan) := do
  match sourceEq : source.resolveScoped with
  | .error reason => throw reason
  | .ok caller =>
    match boundEq : bound.resolveScoped with
    | .error reason => throw reason
    | .ok closed =>
      match checked : checkScopedBoundary source bound caller closed plan with
      | .error reason => throw reason
      | .ok exposed =>
        if equal : exposed = closed.hideSlots (scopedSlots caller) then
          return ⟨caller, closed, exposed, sourceEq, boundEq, checked, equal⟩
        else throw "Binding changed a caller instruction or ordered actual"

/-- The checker accepts exactly the pairs related by resolution, reconstruction and
opaque comparison. This is a structural relation on decoded programs. -/
theorem verifyScopedSourceLink_iff {source bound : Program} {plan : ScopedCapturePlan} :
    (verifyScopedSourceLink source bound plan).isOk = true ↔
    ∃ caller closed exposed : ScopedProgram,
      source.resolveScoped = .ok caller ∧ bound.resolveScoped = .ok closed ∧
      checkScopedBoundary source bound caller closed plan = .ok exposed ∧
      exposed = closed.hideSlots (scopedSlots caller) := by
  constructor
  · intro accepted
    cases result : verifyScopedSourceLink source bound plan with
    | error reason =>
      rw [result] at accepted
      cases accepted
    | ok link =>
      exact ⟨link.caller, link.closed, link.exposed, link.source_resolved, link.bound_resolved,
        link.rebuilt, link.checked⟩
  · rintro ⟨caller, closed, exposed, sourceResolved, boundResolved, rebuilt, equal⟩
    unfold verifyScopedSourceLink
    split
    · rename_i reason rejected
      rw [sourceResolved] at rejected
      contradiction
    · rename_i actual resolved
      have same := Except.ok.inj (resolved.symm.trans sourceResolved)
      subst actual
      split
      · rename_i reason rejected
        rw [boundResolved] at rejected
        contradiction
      · rename_i actual resolved
        have same := Except.ok.inj (resolved.symm.trans boundResolved)
        subst actual
        split
        · rename_i reason rejected
          rw [rebuilt] at rejected
          contradiction
        · rename_i actual reconstructed
          have same := Except.ok.inj (reconstructed.symm.trans rebuilt)
          subst actual
          rw [dite_eq_left equal]
          rfl

noncomputable def Program.scopedMatrix (source : Program) (snapshot : Snapshot) :
    Except String (Σ n : Nat, WireMatrix n) := do
  let graph ← source.resolveScoped
  return ⟨graph.entryWires, ← graph.matrixWith snapshot⟩

theorem Program.scopedMatrix_of_resolved {source : Program} {graph : ScopedProgram}
    {snapshot : Snapshot} {matrix : WireMatrix graph.entryWires}
    (resolved : source.resolveScoped = .ok graph)
    (evaluated : graph.matrixWith snapshot = .ok matrix) :
    source.scopedMatrix snapshot = .ok ⟨graph.entryWires, matrix⟩ := by
  simp [Program.scopedMatrix, resolved, evaluated, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem Program.resolved_of_scopedMatrix {source : Program} {graph : ScopedProgram}
    {snapshot : Snapshot} {matrix : WireMatrix graph.entryWires}
    (resolved : source.resolveScoped = .ok graph)
    (evaluated : source.scopedMatrix snapshot = .ok ⟨graph.entryWires, matrix⟩) :
    graph.matrixWith snapshot = .ok matrix := by
  cases computed : graph.matrixWith snapshot <;>
    simp_all [Program.scopedMatrix, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The decoded bound program agrees with a successful execution of the
reconstructed caller under the selected oracle contracts. -/
theorem ScopedSourceLink.sound {source bound : Program} {plan : ScopedCapturePlan}
    (link : ScopedSourceLink source bound plan) (snapshot : Snapshot) (oracle : ScopedOracle)
    (contracts : ScopedContracts (scopedSlots link.caller) oracle [] link.closed.modules)
    {matrix : WireMatrix link.exposed.entryWires}
    (expected : link.exposed.matrixWith snapshot (scopedSlots link.caller) oracle = .ok matrix) :
    bound.scopedMatrix snapshot = .ok ⟨link.exposed.entryWires, matrix⟩ := by
  cases link with
  | mk caller closed exposed src boundEq rebuilt checked =>
    cases checked
    rw [closed.hideSlots_matrix] at expected
    have applied := closed.substitute snapshot (scopedSlots caller) oracle contracts _ expected
    simp [Program.scopedMatrix, boundEq, applied, Bind.bind, Except.bind, Pure.pure, Except.pure,
      ScopedProgram.hideSlots]

end OracqVerify.RIR
