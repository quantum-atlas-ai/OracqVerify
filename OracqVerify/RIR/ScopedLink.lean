module

public import OracqVerify.RIR.ScopedPlacement

/-! Interpreting a scoped module table and substituting specifications for bound slots. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Classical

/-- Rebase a typed snapshot onto the lexical names of the callee. Matching of
formals to actuals is positional, and different formals may alias one bank. -/
def Snapshot.forward (formals actuals : List Resource) (parent : Snapshot) :
    Except String Snapshot :=
  if formals.map Resource.type = actuals.map Resource.type then
    .ok fun formal =>
      match (formals.zip actuals).find? (fun pair => decide (pair.1 = formal)) with
      | none => none
      | some (_, actual) =>
        if same : actual.type = formal.type then
          same ▸ parent actual
        else none
  else .error "Scoped call bank interface mismatch"

/-- A lookup in a successfully forwarded snapshot uses exactly the selected actual bank. -/
theorem Snapshot.forward_bank {formals actuals : List Resource} {parent child : Snapshot}
    (forwarded : parent.forward formals actuals = .ok child)
    {formal actual : Resource}
    (selected : (formals.zip actuals).find? (fun pair => decide (pair.1 = formal)) =
      some (formal, actual)) (same : actual.type = formal.type) :
    child formal = same ▸ parent actual := by
  unfold Snapshot.forward at forwarded
  split at forwarded
  · cases forwarded
    simp [selected, same]
  · cases forwarded

abbrev ScopedMeaning (m : ScopedModule) := Snapshot → Except String (WireMatrix m.publicWires)

structure ScopedDefinition where
  publicWires : Nat
  banks : List Resource
  apply : Snapshot → Except String (WireMatrix publicWires)

abbrev ScopedEnvironment := List (String × ScopedDefinition)

/-- Place a previously interpreted callee in its caller's frame after rebasing
the memory snapshot. Every call evaluates the callee in its own snapshot. -/
noncomputable def ScopedEnvironment.atCall (environment : ScopedEnvironment) (width : Nat)
    (snapshot : Snapshot) : Oracle width := fun site => do
  let child ← lookup environment site.name "scoped callee"
  let view ← View.ofWires width child.publicWires site.arguments.flatten
  let forwarded ← snapshot.forward child.banks site.banks
  let body ← child.apply forwarded
  return view.placeMatrix body

/-- Interpret a concrete definition with a clean-exit check. This denotation is
noncomputable, and a proof can discharge both checks via `Certificate`. -/
noncomputable def ScopedModule.interpret (m : ScopedModule) (environment : ScopedEnvironment) :
    ScopedMeaning m := fun snapshot => do
  let matrix ← m.bodyMatrix snapshot (environment.atCall m.width snapshot)
  if matrix ∈ Matrix.unitaryGroup (Reg m.width) ℂ ∧ m.Clean matrix then
    return m.publicMatrix matrix
  else throw s!"Missing clean unitary exit at {m.name}"

/-- A specification for an oracle's public action in its lexical bank frame. -/
abbrev ScopedOracle := (name : String) → (width : Nat) →
  Snapshot → Except String (WireMatrix width)

noncomputable def ScopedEnvironment.extend (known : ScopedEnvironment) (m : ScopedModule)
    (slots : List String) (oracle : ScopedOracle) : ScopedEnvironment :=
  let meaning := if slots.contains m.name then oracle m.name m.publicWires else m.interpret known
  (m.name, ⟨m.publicWires, m.banks, meaning⟩) :: known

/-- Interpret one definition per node in postorder. The environment stores
functions of snapshots so a shared definition can receive distinct banks. -/
noncomputable def scopedEnvironment (modules : List ScopedModule)
    (slots : List String) (oracle : ScopedOracle)
    (initial : ScopedEnvironment := []) : ScopedEnvironment :=
  modules.foldl (fun known m => known.extend m slots oracle) initial

def unboundScopedOracle : ScopedOracle := fun name _ _ => .error s!"Unbound scoped slot {name}"

noncomputable def ScopedProgram.matrixWith (program : ScopedProgram) (snapshot : Snapshot)
    (slots : List String := []) (oracle : ScopedOracle := unboundScopedOracle) :
    Except String (WireMatrix program.entryWires) := do
  let environment := scopedEnvironment program.modules slots oracle
  let entry ← lookup environment program.entry "scoped entry"
  if width : entry.publicWires = program.entryWires then
    return width ▸ (← entry.apply snapshot)
  else throw "Scoped entry width mismatch"

theorem ScopedModule.Certificate.interpret {m : ScopedModule} {snapshot : Snapshot}
    {known : ScopedEnvironment} {u : WireMatrix m.width}
    (certificate : m.Certificate snapshot (known.atCall m.width snapshot) u) :
    m.interpret known snapshot = .ok (m.publicMatrix u) := by
  simp [ScopedModule.interpret, certificate.body, certificate.unitary, certificate.clean,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A concrete evaluation preserves each successful result of the specification. -/
abbrev ScopedRefines {A : Type} (specification concrete : Except String A) : Prop :=
  ∀ result, specification = .ok result → concrete = .ok result

private theorem ScopedRefines.refl {A : Type} (value : Except String A) :
    ScopedRefines value value := fun _ done => done

private theorem ScopedRefines.bind {A B : Type} {first second : Except String A}
    {f g : A → Except String B} (before : ScopedRefines first second)
    (after : ∀ x, ScopedRefines (f x) (g x)) :
    ScopedRefines (first >>= f) (second >>= g) := by
  intro result done
  cases first with
  | error reason => cases done
  | ok value =>
    have equal := before value rfl
    rw [equal]
    exact after value result done

private theorem mapM_refines {A B : Type} (f g : A → Except String B) (steps : List A)
    (agrees : ∀ step, ScopedRefines (f step) (g step)) :
    ScopedRefines (steps.mapM f) (steps.mapM g) := by
  induction steps with
  | nil => exact ScopedRefines.refl _
  | cons head tail ih =>
    simp only [List.mapM_cons]
    exact (agrees head).bind (fun _ => ih.bind (fun _ => ScopedRefines.refl _))

private inductive ScopedDefinition.Refines : ScopedDefinition → ScopedDefinition → Prop
  | mk (width : Nat) (banks : List Resource)
      (specification concrete : Snapshot → Except String (WireMatrix width))
      (agrees : ∀ s, ScopedRefines (specification s) (concrete s)) :
      Refines ⟨width, banks, specification⟩ ⟨width, banks, concrete⟩

private abbrev EnvRefines (specification concrete : ScopedEnvironment) : Prop :=
  List.Forall₂ (fun entry actual => entry.1 = actual.1 ∧ entry.2.Refines actual.2)
    specification concrete

private theorem envLookup_refines {specification concrete : ScopedEnvironment}
    (related : EnvRefines specification concrete) (name kind : String)
    {chosen : ScopedDefinition} (found : lookup specification name kind = .ok chosen) :
    ∃ actual, lookup concrete name kind = .ok actual ∧ chosen.Refines actual := by
  induction related with
  | nil => cases found
  | cons first tail ih =>
    rename_i x y xs ys
    obtain ⟨equalName, refinements⟩ := first
    by_cases hit : name == x.1
    · have candidate : name == y.1 := equalName ▸ hit
      have equal : x.2 = chosen := by simpa [lookup, List.lookup, hit] using found
      refine ⟨y.2, ?_, equal ▸ refinements⟩
      simp [lookup, List.lookup, candidate]
    · have candidate : ¬(name == y.1) := equalName ▸ hit
      have rest : lookup xs name kind = .ok chosen := by
        simpa [lookup, List.lookup, hit] using found
      obtain ⟨actual, selected, correct⟩ := ih rest
      refine ⟨actual, ?_, correct⟩
      simpa [lookup, List.lookup, candidate] using selected

private theorem atCall_refines {specification concrete : ScopedEnvironment}
    (related : EnvRefines specification concrete) (width : Nat) (snapshot : Snapshot)
    (site : CallSite) : ScopedRefines (specification.atCall width snapshot site)
      (concrete.atCall width snapshot site) := by
  intro result done
  unfold ScopedEnvironment.atCall at done ⊢
  cases found : lookup specification site.name "scoped callee" with
  | error reason => rw [found] at done; cases done
  | ok child =>
    obtain ⟨other, selected, matching⟩ := envLookup_refines related _ _ found
    rw [found] at done
    rw [selected]
    cases matching with
    | mk k banks source target agrees =>
      have call :
          ScopedRefines
            (do
              let view ← View.ofWires width k site.arguments.flatten
              let forwarded ← snapshot.forward banks site.banks
              let body ← source forwarded
              pure (view.placeMatrix body))
            (do
              let view ← View.ofWires width k site.arguments.flatten
              let forwarded ← snapshot.forward banks site.banks
              let body ← target forwarded
              pure (view.placeMatrix body)) :=
        (ScopedRefines.refl _).bind fun _ => (ScopedRefines.refl _).bind fun forwarded =>
          (agrees forwarded).bind fun _ => ScopedRefines.refl _
      exact call result done

private theorem step_refines (width : Nat) (snapshot : Snapshot) (oracle other : Oracle width)
    (calls : ∀ site, ScopedRefines (oracle site) (other site)) (step : ResolvedInstruction) :
    ScopedRefines (step.matrixWith width snapshot oracle) (step.matrixWith width snapshot other) := by
  induction step with
  | query name arguments banks => exact calls ⟨name, arguments, banks⟩
  | controlled guard step ih =>
    exact (ScopedRefines.refl _).bind fun _ => ih.bind fun _ => ScopedRefines.refl _
  | adjoint step ih => exact ih.bind fun _ => ScopedRefines.refl _
  | unary _ _ | xor _ _ | addConst _ _ | load _ _ _ | gphase _ => exact ScopedRefines.refl _

private theorem interpret_refines {specification concrete : ScopedEnvironment}
    (related : EnvRefines specification concrete) (m : ScopedModule) (snapshot : Snapshot) :
    ScopedRefines (m.interpret specification snapshot) (m.interpret concrete snapshot) := by
  apply ScopedRefines.bind _ (fun _ => ScopedRefines.refl _)
  unfold ScopedModule.bodyMatrix
  cases m.body with
  | none => exact ScopedRefines.refl _
  | some steps =>
    exact (mapM_refines _ _ steps
      (step_refines _ _ _ _ (atCall_refines related _ _))).bind fun _ => ScopedRefines.refl _

/-- A selected implementation must realize a slot on each snapshot where the
abstract specification supplies a result. Its body must clean its workspace. -/
def ScopedContracts (slots : List String) (oracle : ScopedOracle)
    (initial : ScopedEnvironment) : List ScopedModule → Prop
  | [] => True
  | m :: rest =>
    (slots.contains m.name = true → ∀ snapshot, ScopedRefines
      (oracle m.name m.publicWires snapshot) (m.interpret initial snapshot)) ∧
    ScopedContracts slots oracle (initial.extend m [] unboundScopedOracle) rest

private theorem scopedEnvironment_refines {slots : List String} {oracle : ScopedOracle}
    {specification concrete : ScopedEnvironment} {modules : List ScopedModule}
    (related : EnvRefines specification concrete)
    (contracts : ScopedContracts slots oracle concrete modules) :
    EnvRefines (scopedEnvironment modules slots oracle specification)
      (scopedEnvironment modules [] unboundScopedOracle concrete) := by
  induction modules generalizing specification concrete with
  | nil => exact related
  | cons m rest ih =>
    simp only [scopedEnvironment, List.foldl_cons]
    apply ih _ contracts.2
    apply List.Forall₂.cons _ related
    refine ⟨rfl, ?_⟩
    cases selected : slots.contains m.name with
    | true =>
      simpa only [ScopedEnvironment.extend, selected, ite_true, List.contains_nil,
        Bool.false_eq_true, ite_false] using
        ScopedDefinition.Refines.mk m.publicWires m.banks _ _ (contracts.1 selected)
    | false =>
      simpa only [ScopedEnvironment.extend, selected, List.contains_nil, Bool.false_eq_true,
        ite_false] using ScopedDefinition.Refines.mk m.publicWires m.banks _ _
          (interpret_refines related m)

/-- Every successful abstract execution has the same full matrix in the
bound program, including phase in controlled and adjointed contexts. -/
theorem ScopedProgram.substitute (program : ScopedProgram) (snapshot : Snapshot)
    (slots : List String) (oracle : ScopedOracle)
    (contracts : ScopedContracts slots oracle [] program.modules) :
    ScopedRefines (program.matrixWith snapshot slots oracle) (program.matrixWith snapshot) := by
  intro result done
  dsimp only [ScopedProgram.matrixWith] at done ⊢
  have environments := scopedEnvironment_refines List.Forall₂.nil contracts
  cases found : lookup (scopedEnvironment program.modules slots oracle) program.entry "scoped entry" with
  | error reason => rw [found] at done; cases done
  | ok entry =>
    obtain ⟨other, selected, matching⟩ := envLookup_refines environments _ _ found
    rw [found] at done
    rw [selected]
    cases matching with
    | mk width banks source target agrees =>
      by_cases same : width = program.entryWires
      · subst width
        cases evaluated : source snapshot with
        | error reason => simp [Bind.bind, Except.bind, evaluated] at done
        | ok value =>
          have actual := agrees snapshot value evaluated
          have equal : value = result := by
            simpa [Bind.bind, Except.bind, evaluated, Pure.pure, Except.pure] using done
          simp [Bind.bind, Except.bind, actual, equal, Pure.pure, Except.pure]
      · have failure : ¬ width = program.entryWires := same
        simp [Bind.bind, Except.bind, failure] at done

/-- Erase the implementations at the oracle boundary. -/
def ScopedModule.hideSlot (slots : List String) (m : ScopedModule) : ScopedModule :=
  if slots.contains m.name then { m with body := none } else m

def ScopedProgram.hideSlots (program : ScopedProgram) (slots : List String) : ScopedProgram :=
  { program with modules := program.modules.map (ScopedModule.hideSlot slots) }

private theorem scopedEnvironment_hideSlots (modules : List ScopedModule) (slots : List String)
    (oracle : ScopedOracle) (initial : ScopedEnvironment) :
    scopedEnvironment (modules.map (ScopedModule.hideSlot slots)) slots oracle initial =
      scopedEnvironment modules slots oracle initial := by
  induction modules generalizing initial with
  | nil => rfl
  | cons m rest ih =>
    have head : initial.extend (m.hideSlot slots) slots oracle = initial.extend m slots oracle := by
      by_cases selected : slots.contains m.name = true
      · unfold ScopedModule.hideSlot
        rw [ite_eq_left selected]
        simp only [ScopedEnvironment.extend, selected, ite_true]
      · unfold ScopedModule.hideSlot
        rw [ite_eq_right selected]
    simp only [scopedEnvironment, List.map_cons, List.foldl_cons, head]
    exact ih _

theorem ScopedProgram.hideSlots_matrix (program : ScopedProgram) (snapshot : Snapshot)
    (slots : List String) (oracle : ScopedOracle) :
    (program.hideSlots slots).matrixWith snapshot slots oracle =
      program.matrixWith snapshot slots oracle := by
  simp only [ScopedProgram.matrixWith, ScopedProgram.hideSlots, scopedEnvironment_hideSlots]
  rfl

end OracqVerify.RIR
