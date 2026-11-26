module

public import OracqVerify.RIR.Semantics

/-! Sparse action of the single-wire RIR gates and controlled phases, on exact or executable scalars. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

/-- Rows are applied in the physical wire basis, with at most two input amplitudes per gate. -/
inductive GateAction (n : Nat) where
  | unary (gate : UnaryGate) (wire : Fin n) (inverse : Bool)
  | phase (angle : Lean.JsonNumber) (inverse : Bool)
  | control {width : Nat} (view : View n width) (value : Nat) (body : GateAction n)

/-- Compile the phase and single-wire fragment, pushing adjoints down to individual gates. -/
def GateAction.lower (n : Nat) (inverse : Bool) : ResolvedInstruction → Except String (GateAction n)
  | .unary gate [wire] =>
    if h : wire < n then .ok (.unary gate ⟨wire, h⟩ inverse) else .error "Wire out of bounds"
  | .gphase angle => .ok (.phase angle inverse)
  | .controlled guard body => do
    let view ← View.ofWires n guard.wires.length guard.wires
    return .control view guard.value (← lower n inverse body)
  | .adjoint body => lower n (!inverse) body
  | _ => .error "Expected a single-wire gate or phase"

def updateBit {n : Nat} (row : Reg n) (wire : Fin n) (bit : Bool) : Reg n :=
  Function.update row wire bit

/-- Compare precisely the bits of a guard, in its resolved order. -/
def guardEnabled {n k : Nat} (view : View n k) (value : Nat) (row : Reg n) : Bool :=
  (List.finRange k).all fun i => row (view i) == value.testBit i.val

theorem guardEnabled_spec {n k : Nat} (view : View n k) (value : Nat) (row : Reg n) :
    guardEnabled view value row = true ↔ matchesGuard view value row := by
  simp [guardEnabled, matchesGuard, List.all_eq_true]

/-- Table of coefficients, with inverse entries supplied by the chosen scalar interpretation. -/
structure GateCoefficients (α : Type) where
  zero : α
  add : α → α → α
  mul : α → α → α
  unary : UnaryGate → Bool → Bool → Bool → α
  phase : Lean.JsonNumber → Bool → α

/-- Apply one gate to a state. A control replaces the inactive input sector by zero when
evaluating the active block, matching the matrix definition even before checking disjointness. -/
def GateAction.apply {α : Type} {n : Nat} (coeff : GateCoefficients α)
    (state : Reg n → α) : GateAction n → Reg n → α
  | .unary gate wire inv => fun row =>
    coeff.add (coeff.mul (coeff.unary gate inv (row wire) false) (state (updateBit row wire false)))
      (coeff.mul (coeff.unary gate inv (row wire) true) (state (updateBit row wire true)))
  | .phase angle inv => fun row => coeff.mul (coeff.phase angle inv) (state row)
  | .control view value body => fun row =>
    if guardEnabled view value row then
      body.apply coeff (fun col => if guardEnabled view value col then state col else coeff.zero) row
    else state row

noncomputable def GateCoefficients.exact : GateCoefficients ℂ where
  zero := 0
  add := (· + ·)
  mul := (· * ·)
  unary gate inv row col := (if inv then (unaryMatrix gate)ᴴ else unaryMatrix gate) row col
  phase angle inv :=
    let phase := Complex.exp ((angleValue angle : ℂ) * Complex.I)
    if inv then star phase else phase

noncomputable def GateAction.matrix {n : Nat} : GateAction n → WireMatrix n
  | .unary gate wire inv => atWire wire (fun row col => GateCoefficients.exact.unary gate inv row col)
  | .phase angle inv => diagonal (fun _ => GateCoefficients.exact.phase angle inv)
  | .control view value body => controlledMatrix (matchesGuard view value) body.matrix

theorem atWire_adjoint {n : Nat} (wire : Fin n) (u : Matrix Bool Bool ℂ) :
    (atWire wire u)ᴴ = atWire wire uᴴ := by
  ext row col
  have h :
      (∀ i : Fin n, i ≠ wire → col i = row i) ↔ (∀ i : Fin n, i ≠ wire → row i = col i) :=
    ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
  simp only [conjTranspose_apply, atWire, h]
  split <;> simp

private theorem singleView {n : Nat} (wire : Fin n) :
    View.ofWires n 1 [wire.val] =
      .ok ⟨fun _ => wire, fun _ _ _ => Subsingleton.elim _ _⟩ := by
  unfold View.ofWires
  split
  · dsimp only
    split
    · split
      · congr 1
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      · rename_i hn
        exact False.elim (hn fun i j _ => Subsingleton.elim i j)
    · rename_i hn
      apply False.elim (hn ?_)
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact wire.isLt
  · contradiction

theorem GateAction.lower_matrix {n : Nat} (snapshot : Snapshot)
    {step : ResolvedInstruction} {inv : Bool} {action : GateAction n}
    (h : GateAction.lower n inv step = .ok action) :
    step.matrix n snapshot = .ok (if inv then action.matrixᴴ else action.matrix) := by
  induction step generalizing inv action with
  | unary gate wires =>
    cases wires with
    | nil => contradiction
    | cons wire rest =>
      cases rest with
      | cons => contradiction
      | nil =>
        simp only [lower] at h
        split at h
        · rename_i hw
          cases h
          have hv := singleView (⟨wire, hw⟩ : Fin n)
          cases inv <;>
            simp [ResolvedInstruction.matrix, Bind.bind, Except.bind, Pure.pure, Except.pure,
              hv, matrix, GateCoefficients.exact, wordMatrix, List.finRange]
          · rfl
          · change atWire ⟨wire, hw⟩ (unaryMatrix gate) =
              (atWire ⟨wire, hw⟩ (unaryMatrix gate)ᴴ)ᴴ
            rw [atWire_adjoint, conjTranspose_conjTranspose]
        · contradiction
  | gphase angle =>
    cases h
    cases inv <;> simp [ResolvedInstruction.matrix, matrix, GateCoefficients.exact, globalPhase,
      diagonal_conjTranspose]
  | xor | addConst | load | query => contradiction
  | controlled guard body ih =>
    simp only [lower, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i view hv
      split at h
      · contradiction
      · rename_i child hc
        cases h
        cases inv <;> simp_all [ResolvedInstruction.matrix, Bind.bind, Except.bind, Pure.pure,
          Except.pure, matrix, controlledMatrix_adjoint]
  | adjoint body ih =>
    have hb := ih h
    cases inv <;> simp_all [ResolvedInstruction.matrix, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

theorem atWire_apply {n : Nat} (wire : Fin n) (u : Matrix Bool Bool ℂ) (ψ : QState (Reg n))
    (row : Reg n) :
    ApplyGate (atWire wire u) ψ row =
      u (row wire) false * ψ (updateBit row wire false) +
        u (row wire) true * ψ (updateBit row wire true) := by
  classical
  let e := Equiv.funSplitAt wire Bool
  change (∑ col, atWire wire u row col * ψ col) = _
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  have hs (b : Bool) : e.symm (b, (e row).2) = updateBit row wire b := by
    funext i
    by_cases hi : i = wire
    · subst i
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, updateBit]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, updateBit, hi]
  have hsum (b : Bool) :
      (∑ s : { j // j ≠ wire } → Bool, atWire wire u row (e.symm (b, s)) * ψ (e.symm (b, s))) =
        u (row wire) b * ψ (updateBit row wire b) := by
    rw [← hs]
    rw [Finset.sum_eq_single (e row).2]
    · simp [atWire, e, Equiv.funSplitAt, Equiv.piSplitAt]
    · intro s _ hn
      have h : ¬ ∀ i : Fin n, i ≠ wire → row i = e.symm (b, s) i := by
        intro h
        apply hn
        funext i
        simpa [e, Equiv.funSplitAt, Equiv.piSplitAt, i.property] using (h i i.property).symm
      simp [atWire, h]
    · simp
  rw [hsum false, hsum true]
  exact add_comm _ _

theorem controlledMatrix_apply {I : Type} [Fintype I] [DecidableEq I]
    (guard : I → Prop) [DecidablePred guard] (u : Matrix I I ℂ) (ψ : QState I) (row : I) :
    ApplyGate (controlledMatrix guard u) ψ row =
      if guard row then ApplyGate u (fun col => if guard col then ψ col else 0) row else ψ row := by
  classical
  by_cases hr : guard row
  · simp only [hr, ite_true, ApplyGate, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro col _
    by_cases hc : guard col
    · simp [controlledMatrix, hr, hc]
    · have hn : row ≠ col := fun e => hc (e ▸ hr)
      simp [controlledMatrix, hr, hc, hn]
  · have h (col : I) : controlledMatrix guard u row col = (1 : Matrix I I ℂ) row col := by
      simp [controlledMatrix, hr]
    simp only [hr, ite_false]
    change (∑ col, controlledMatrix guard u row col * ψ col) = _
    simp only [h]
    exact congrFun (Matrix.one_mulVec ψ) row

theorem GateAction.apply_exact {n : Nat} (step : GateAction n) (ψ : QState (Reg n)) :
    step.apply GateCoefficients.exact ψ = ApplyGate step.matrix ψ := by
  induction step generalizing ψ with
  | unary =>
    funext row
    exact (atWire_apply ..).symm
  | phase angle inv =>
    funext row
    change GateCoefficients.exact.phase angle inv * ψ row =
      ((diagonal (fun _ : Reg n => GateCoefficients.exact.phase angle inv)) *ᵥ ψ) row
    rw [Matrix.mulVec_diagonal]
  | control view value body ih =>
    classical
    funext row
    rw [GateAction.apply, GateAction.matrix, controlledMatrix_apply]
    simp only [guardEnabled_spec, show GateCoefficients.exact.zero = 0 from rfl, ih]

/-- Traverse the lowered gates in the same execution order as the resolved RIR. -/
def GateAction.run {α : Type} {n : Nat} (coeff : GateCoefficients α) :
    List (GateAction n) → (Reg n → α) → Reg n → α
  | [], state => state
  | step :: rest, state => run coeff rest (step.apply coeff state)

theorem GateAction.run_exact {n : Nat} (steps : List (GateAction n)) (ψ : QState (Reg n)) :
    GateAction.run GateCoefficients.exact steps ψ = ApplyGate (wordMatrix (steps.map matrix)) ψ := by
  induction steps generalizing ψ with
  | nil => simp [run, wordMatrix, ApplyGate]
  | cons step rest ih =>
    rw [run, step.apply_exact, ih]
    simp [wordMatrix, ApplyGate, Matrix.mulVec_mulVec]

theorem GateAction.lower_word_matrix {n : Nat} (snapshot : Snapshot)
    {steps : List ResolvedInstruction} {actions : List (GateAction n)}
    (h : steps.mapM (lower n false) = .ok actions) :
    steps.mapM (ResolvedInstruction.matrix n snapshot) = .ok (actions.map matrix) := by
  induction steps generalizing actions with
  | nil => cases h; rfl
  | cons step rest ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i action hs
      split at h
      · contradiction
      · rename_i tail ht
        cases h
        simp [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, lower_matrix snapshot hs,
          ih ht]

theorem GateAction.resolved_matrix {program : ResolvedProgram} (snapshot : Snapshot)
    {actions : List (GateAction program.wireCount)}
    (h : program.instructions.mapM (lower program.wireCount false) = .ok actions) :
    program.matrix snapshot = .ok (wordMatrix (actions.map matrix)) := by
  simp [ResolvedProgram.matrix, Bind.bind, Except.bind, Pure.pure, Except.pure,
    lower_word_matrix snapshot h]

end OracqVerify.RIR
