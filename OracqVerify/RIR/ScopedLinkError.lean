module

public import OracqVerify.RIR.LinkError
public import OracqVerify.RIR.ScopedSourceLink

/-! Assemble quantitative contracts over a shared scoped call graph. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

abbrev ScopedBudgetTable := List (String × (Snapshot → ℝ))

/-- Charge a callee in its own lexical snapshot. On an unresolved call no
budget is needed: the comparison theorem concerns successful executions. -/
noncomputable def ScopedEnvironment.callError (ref : ScopedEnvironment)
    (budget : ScopedBudgetTable) (snapshot : Snapshot) (site : CallSite) : ℝ :=
  let result : Except String ℝ := do
    let child ← lookup ref site.name "scoped callee"
    let cost ← lookup budget site.name "scoped budget"
    let memory ← snapshot.forward child.banks site.banks
    return cost memory
  result.toOption.getD 0

/-- A budget table shares the two environments' order and interfaces. Each
entry proves a public norm bound in the callee's own snapshot. -/
inductive ScopedErrorEvidence :
    ScopedEnvironment → ScopedEnvironment → ScopedBudgetTable → Prop
  | nil : ScopedErrorEvidence [] [] []
  | cons {left right : ScopedEnvironment} {budgets : ScopedBudgetTable}
      (previous : ScopedErrorEvidence left right budgets)
      (name : String) (width : Nat) (banks : List Resource)
      (ref impl : Snapshot → Except String (WireMatrix width)) (cost : Snapshot → ℝ)
      (contract : ∀ s u v, ref s = .ok u → impl s = .ok v → ‖u - v‖ ≤ cost s) :
      ScopedErrorEvidence ((name, ⟨width, banks, ref⟩) :: left)
        ((name, ⟨width, banks, impl⟩) :: right) ((name, cost) :: budgets)

private theorem ScopedErrorEvidence.lookup {ref impl : ScopedEnvironment} {budgets : ScopedBudgetTable}
    (evidence : ScopedErrorEvidence ref impl budgets) (name kind : String) {left : ScopedDefinition}
    (found : RIR.lookup ref name kind = .ok left) :
    ∃ (right : ScopedDefinition) (cost : Snapshot → ℝ) (width : Nat) (banks : List Resource)
      (a b : Snapshot → Except String (WireMatrix width)),
      left = ⟨width, banks, a⟩ ∧ right = ⟨width, banks, b⟩ ∧
      RIR.lookup impl name kind = .ok right ∧ RIR.lookup budgets name "scoped budget" = .ok cost ∧
      ∀ s u v, a s = .ok u → b s = .ok v → ‖u - v‖ ≤ cost s := by
  induction evidence with
  | nil => cases found
  | @cons ref impl budgets previous key width banks a b cost contract ih =>
    by_cases hit : name == key
    · have same : (⟨width, banks, a⟩ : ScopedDefinition) = left := by
        simpa [RIR.lookup, List.lookup, hit] using found
      exact ⟨⟨width, banks, b⟩, cost, width, banks, a, b, same.symm, rfl,
        by simp [RIR.lookup, List.lookup, hit],
        by simp [RIR.lookup, List.lookup, hit], contract⟩
    · have tail : RIR.lookup ref name kind = .ok left := by
        simpa [RIR.lookup, List.lookup, hit] using found
      obtain ⟨right, expense, k, handles, a, b, spec, actual, selected, budget, bound⟩ := ih tail
      exact ⟨right, expense, k, handles, a, b, spec, actual,
        by simpa [RIR.lookup, List.lookup, hit] using selected,
        by simpa [RIR.lookup, List.lookup, hit] using budget, bound⟩

/-- The same charged error applies to a call under its actual wire and bank arguments. -/
theorem ScopedErrorEvidence.atCall {ref impl : ScopedEnvironment} {budgets : ScopedBudgetTable}
    (evidence : ScopedErrorEvidence ref impl budgets) (width : Nat) (s : Snapshot)
    (site : CallSite) (u v : WireMatrix width)
    (left : ref.atCall width s site = .ok u) (right : impl.atCall width s site = .ok v) :
    ‖u - v‖ ≤ ref.callError budgets s site := by
  cases found : RIR.lookup ref site.name "scoped callee" with
  | error reason =>
    simp [ScopedEnvironment.atCall, found, Bind.bind, Except.bind] at left
  | ok child =>
    obtain ⟨other, cost, k, banks, a, b, rfl, rfl, selected, charged, contract⟩ :=
      evidence.lookup _ _ found
    cases rebased : s.forward banks site.banks with
    | error reason =>
      unfold ScopedEnvironment.atCall at left
      cases placed : View.ofWires width k site.arguments.flatten <;>
        simp [found, placed, rebased, Bind.bind, Except.bind] at left
    | ok memory =>
      have budget : ref.callError budgets s site = cost memory := by
        simp [ScopedEnvironment.callError, found, charged, rebased, Bind.bind, Except.bind,
          Pure.pure, Except.pure, Except.toOption]
      rw [budget]
      exact ScopedEnvironment.atCall_distance ref impl site s banks a b found selected memory
        rebased (cost memory) (contract memory) left right

private theorem interpreted {m : ScopedModule} {environment : ScopedEnvironment}
    {s : Snapshot} {v : WireMatrix m.publicWires}
    (done : m.interpret environment s = .ok v) :
    ∃ u, m.Certificate s (environment.atCall m.width s) u ∧ m.publicMatrix u = v := by
  unfold ScopedModule.interpret at done
  cases evaluated : m.bodyMatrix s (environment.atCall m.width s) with
  | error reason => simp [evaluated, Bind.bind, Except.bind] at done
  | ok u =>
    by_cases h : u ∈ Matrix.unitaryGroup (Reg m.width) ℂ ∧ m.Clean u
    · have equal : m.publicMatrix u = v := by
        simpa [evaluated, h, Bind.bind, Except.bind, Pure.pure, Except.pure] using done
      exact ⟨u, ⟨evaluated, h.1, h.2⟩, equal⟩
    · simp [evaluated, h, Bind.bind, Except.bind] at done

/-- Extend a budget table by a retained body. The new function charges each
call in that body using the table of already interpreted dependencies. -/
theorem ScopedErrorEvidence.extendBody
    {ref impl : ScopedEnvironment} {budgets : ScopedBudgetTable}
    (evidence : ScopedErrorEvidence ref impl budgets) (m : ScopedModule)
    (steps : List ResolvedInstruction) (body : m.body = some steps)
    (contractions : ∀ s step, step ∈ steps → ∀ u v,
      step.matrixWith m.width s (ref.atCall m.width s) = .ok u →
      step.matrixWith m.width s (impl.atCall m.width s) = .ok v → ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1) :
    let cost := fun s => (steps.map (ResolvedInstruction.callBudget (ref.callError budgets s))).sum
    ScopedErrorEvidence ((m.name, ⟨m.publicWires, m.banks, m.interpret ref⟩) :: ref)
      ((m.name, ⟨m.publicWires, m.banks, m.interpret impl⟩) :: impl)
      ((m.name, cost) :: budgets) := by
  refine .cons evidence _ _ _ _ _ _ ?_
  intro s v actual left right
  obtain ⟨u, hu, rfl⟩ := interpreted left
  obtain ⟨w, hw, rfl⟩ := interpreted right
  exact m.distance_le s _ _ _ (evidence.atCall m.width s) steps body (contractions s) hu hw

/-- The accepted binding ties the quantitative table to both decoded programs.
As in the body rule, the bounds apply where both interpretations succeed. -/
theorem ScopedSourceLink.distance_le {source bound : Program} {plan : ScopedCapturePlan}
    (link : ScopedSourceLink source bound plan) (snapshot : Snapshot) (oracle : ScopedOracle)
    (budgets : ScopedBudgetTable)
    (evidence : ScopedErrorEvidence
      (scopedEnvironment link.exposed.modules (scopedSlots link.caller) oracle)
      (scopedEnvironment link.closed.modules [] unboundScopedOracle) budgets)
    (cost : Snapshot → ℝ) (charged : lookup budgets link.exposed.entry "scoped budget" = .ok cost)
    {u v : WireMatrix link.exposed.entryWires}
    (left : link.exposed.matrixWith snapshot (scopedSlots link.caller) oracle = .ok u)
    (right : bound.scopedMatrix snapshot = .ok ⟨link.exposed.entryWires, v⟩) :
    ‖u - v‖ ≤ cost snapshot := by
  cases link with
  | mk caller closed exposed src boundEq rebuilt checked =>
    subst exposed
    change WireMatrix closed.entryWires at u v
    change ScopedErrorEvidence
      (scopedEnvironment (closed.hideSlots (scopedSlots caller)).modules (scopedSlots caller) oracle)
      (scopedEnvironment closed.modules [] unboundScopedOracle) budgets at evidence
    have actual : closed.matrixWith snapshot = .ok v :=
      Program.resolved_of_scopedMatrix boundEq right
    change (do
      let entry ← lookup (scopedEnvironment (closed.hideSlots (scopedSlots caller)).modules
        (scopedSlots caller) oracle) closed.entry "scoped entry"
      if width : entry.publicWires = closed.entryWires then
        return width ▸ (← entry.apply snapshot)
      else throw "Scoped entry width mismatch") = .ok u at left
    unfold ScopedProgram.matrixWith at actual
    dsimp only at actual
    cases found : lookup (scopedEnvironment (closed.hideSlots (scopedSlots caller)).modules
        (scopedSlots caller) oracle) closed.entry "scoped entry" with
    | error reason => rw [found] at left; cases left
    | ok root =>
      obtain ⟨other, expense, k, banks, a, b, rfl, rfl, selected, budget, contract⟩ :=
        evidence.lookup _ _ found
      have costEq : expense = cost := Except.ok.inj (budget.symm.trans charged)
      subst expense
      rw [found] at left
      rw [selected] at actual
      by_cases h : k = closed.entryWires
      · subst k
        cases eu : a snapshot <;> cases ev : b snapshot <;>
          simp [eu, ev, Bind.bind, Except.bind, Pure.pure, Except.pure] at left actual
        subst u
        subst v
        exact contract snapshot _ _ eu ev
      · simp [h, Bind.bind, Except.bind] at left

end OracqVerify.RIR
