module

public import OracqVerify.RIR.Semantics
public import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-! Unitary gate words and isometric compression onto a chosen RIR basis frame. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath Qatlib.Concepts.Execution.WorkspaceCP
open scoped Classical Matrix Matrix.Norms.L2Operator

theorem rotationY_unitary (angle : ℝ) : rotationY angle ∈ unitaryGroup Bool ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, rotationY_adjoint]
  ext row col
  have h : (Real.sin (angle / 2) : ℂ) ^ 2 + (Real.cos (angle / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (angle / 2)
  cases row <;> cases col <;>
    simp only [mul_apply, Fintype.sum_bool, one_apply,
      rotationY, neg_div, Real.cos_neg, Real.sin_neg, Bool.false_eq_true, Bool.true_eq_false,
      eq_self, ite_true, ite_false, Complex.ofReal_neg, neg_neg] <;>
    first | linear_combination h | ring

theorem unaryMatrix_unitary (gate : UnaryGate) : unaryMatrix gate ∈ unitaryGroup Bool ℂ := by
  cases gate
  · exact hadamard_unitary
  · exact pauliX_unitary
  · exact pauliZ_unitary
  · exact rotationY_unitary _

theorem atWire_unitary {n : Nat} (wire : Fin n) {gate : Matrix Bool Bool ℂ}
    (h : gate ∈ unitaryGroup Bool ℂ) : atWire wire gate ∈ unitaryGroup (Reg n) ℂ := by
  let e := Equiv.funSplitAt wire Bool
  have he : atWire wire gate =
      reindex e.symm e.symm (TensorGate gate (1 : Matrix ({j // j ≠ wire} → Bool) _ ℂ)) := by
    ext a b
    have hs : (e a).2 = (e b).2 ↔ ∀ i : Fin n, i ≠ wire → a i = b i := by
      constructor
      · intro h i hi
        exact congrFun h ⟨i, hi⟩
      · intro h
        funext i
        exact h i i.property
    change (if ∀ i : Fin n, i ≠ wire → a i = b i then gate (a wire) (b wire) else 0) =
      gate (a wire) (b wire) * (1 : Matrix ({j // j ≠ wire} → Bool) _ ℂ) (e a).2 (e b).2
    simp only [one_apply, hs]
    split <;> simp_all
  rw [he]
  exact Qatlib.Concepts.BlockEncoding.StateBlockEncoding.unitaryGroup_reindex e.symm
    (tensorGate_unitary h (unitaryGroup _ _).one_mem)

theorem globalPhase_unitary (n : Nat) (angle : ℝ) :
    globalPhase n angle ∈ unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro _
  simp [Complex.norm_exp, Complex.mul_re]

theorem controlledMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (active : I → Prop) {gate : Matrix I I ℂ} (h : gate ∈ unitaryGroup I ℂ)
    (preserves : Preserves active gate) :
    controlledMatrix active gate ∈ unitaryGroup I ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose] at h ⊢
  rw [controlledMatrix_adjoint, controlledMatrix_mul active _ _ preserves.adjoint, h,
    controlledMatrix_one]

theorem wordMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (word : List (Matrix I I ℂ)) (h : ∀ gate ∈ word, gate ∈ unitaryGroup I ℂ) :
    wordMatrix word ∈ unitaryGroup I ℂ := by
  induction word with
  | nil => exact (unitaryGroup I ℂ).one_mem
  | cons gate rest ih =>
    exact (unitaryGroup I ℂ).mul_mem (ih (fun u hu => h u (List.mem_cons_of_mem _ hu)))
      (h gate (by simp))

private theorem View.ofWires_mem {n k : Nat} {wires : List Nat} {view : View n k}
    (h : View.ofWires n k wires = .ok view) (i : Fin k) : (view i).val ∈ wires := by
  unfold View.ofWires at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · cases h
        exact List.getElem_mem _
      · contradiction
    · contradiction
  · contradiction

/-- An instruction's potential quantum writes in the gate-only fragment. -/
def ResolvedInstruction.gateTargets : ResolvedInstruction → List Nat
  | .unary _ wires => wires
  | .controlled _ step | .adjoint step => step.gateTargets
  | _ => []

/-- Whether the ordered coordinates realize a typed wire view. -/
def View.isValid (n : Nat) (wires : List Nat) : Bool :=
  (View.ofWires n wires.length wires).toOption.isSome

/-- Check support, wire placement, and disjointness of each control from its instruction's writes. -/
def ResolvedInstruction.isUnitaryGate (n : Nat) : ResolvedInstruction → Bool
  | .unary _ wires => View.isValid n wires
  | .gphase _ => true
  | .controlled guard step =>
    View.isValid n guard.wires &&
      (step.isUnitaryGate n && guard.wires.all (fun wire => !step.gateTargets.contains wire))
  | .adjoint step => step.isUnitaryGate n
  | _ => false

private theorem ResolvedInstruction.gateMatrix_preserves {n k : Nat} (view : View n k)
    (value : Nat) (snapshot : Snapshot) {step : ResolvedInstruction} {u : WireMatrix n}
    (ok : step.isUnitaryGate n = true) (hm : step.matrix n snapshot = .ok u)
    (disjoint : ∀ i : Fin k, (view i).val ∉ step.gateTargets) :
    Preserves (matchesGuard view value) u := by
  induction step generalizing u with
  | unary gate wires =>
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rename_i placed he
      cases hm
      apply wordMatrix_preserves
      simp only [List.mem_map]
      rintro _ ⟨j, _, rfl⟩
      apply atWire_preserves_guard
      intro i hij
      have hmem := View.ofWires_mem he j
      rw [← hij] at hmem
      exact disjoint i hmem
  | gphase angle =>
    cases hm
    exact globalPhase_preserves _ _
  | xor | addConst | load | query => contradiction
  | controlled guard step ih =>
    simp only [ResolvedInstruction.isUnitaryGate, Bool.and_eq_true] at ok
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · split at hm
      · contradiction
      · rename_i gate hg
        cases hm
        exact (ih ok.2.1 hg disjoint).controlled _
  | adjoint step ih =>
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rename_i gate hg
      cases hm
      exact (ih ok hg disjoint).adjoint

theorem ResolvedInstruction.gateMatrix_unitary {n : Nat} (snapshot : Snapshot)
    {step : ResolvedInstruction} {u : WireMatrix n} (ok : step.isUnitaryGate n = true)
    (hm : step.matrix n snapshot = .ok u) : u ∈ unitaryGroup (Reg n) ℂ := by
  induction step generalizing u with
  | unary gate wires =>
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · cases hm
      apply wordMatrix_unitary
      simp only [List.mem_map]
      rintro _ ⟨j, _, rfl⟩
      exact atWire_unitary _ (unaryMatrix_unitary gate)
  | gphase angle =>
    cases hm
    exact globalPhase_unitary _ _
  | xor | addConst | load | query => contradiction
  | controlled guard step ih =>
    simp only [ResolvedInstruction.isUnitaryGate, Bool.and_eq_true] at ok
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rename_i view hv
      split at hm
      · contradiction
      · rename_i gate hg
        cases hm
        apply controlledMatrix_unitary _ (ih ok.2.1 hg)
        apply ResolvedInstruction.gateMatrix_preserves view guard.value snapshot ok.2.1 hg
        intro i
        simpa using List.all_eq_true.mp ok.2.2 _ (View.ofWires_mem hv i)
  | adjoint step ih =>
    simp only [ResolvedInstruction.matrix, Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rename_i gate hg
      cases hm
      rw [← star_eq_conjTranspose]
      exact Unitary.star_mem_iff.mpr (ih ok hg)

private theorem validView_spec {n : Nat} {wires : List Nat} (h : View.isValid n wires = true) :
    ∃ v, View.ofWires n wires.length wires = .ok v := by
  cases hw : View.ofWires n wires.length wires with
  | ok v => exact ⟨v, rfl⟩
  | error reason => simp [View.isValid, hw, Except.toOption] at h

private theorem ResolvedInstruction.gateMatrix_exists {n : Nat} (snapshot : Snapshot)
    {step : ResolvedInstruction} (ok : step.isUnitaryGate n = true) :
    ∃ u, step.matrix n snapshot = .ok u := by
  induction step with
  | unary gate wires =>
    change View.isValid n wires = true at ok
    obtain ⟨view, hv⟩ := validView_spec ok
    refine ⟨wordMatrix ((List.finRange wires.length).map fun i => atWire (view i) (unaryMatrix gate)), ?_⟩
    simp [ResolvedInstruction.matrix, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | gphase => exact ⟨_, rfl⟩
  | xor | addConst | load | query => contradiction
  | controlled guard step ih =>
    simp only [ResolvedInstruction.isUnitaryGate, Bool.and_eq_true] at ok
    obtain ⟨view, hv⟩ := validView_spec ok.1
    obtain ⟨u, hu⟩ := ih ok.2.1
    exact ⟨controlledMatrix (matchesGuard view guard.value) u, by
      simp [ResolvedInstruction.matrix, hv, hu, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  | adjoint step ih =>
    obtain ⟨u, hu⟩ := ih ok
    exact ⟨uᴴ, by simp [ResolvedInstruction.matrix, hu, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- A checked gate-only trace yields a unitary in the exact RIR matrix semantics. -/
theorem ResolvedProgram.gateMatrix_exists (p : ResolvedProgram) (snapshot : Snapshot)
    (ok : p.instructions.all (ResolvedInstruction.isUnitaryGate p.wireCount) = true) :
    ∃ u, p.matrix snapshot = .ok u ∧ u ∈ unitaryGroup (Reg p.wireCount) ℂ := by
  let n := p.wireCount
  suffices h : ∀ steps : List ResolvedInstruction,
      steps.all (ResolvedInstruction.isUnitaryGate n) = true →
      ∃ matrices, steps.mapM (ResolvedInstruction.matrix n snapshot) = .ok matrices ∧
        wordMatrix matrices ∈ unitaryGroup (Reg n) ℂ by
    obtain ⟨matrices, hm, hu⟩ := h p.instructions ok
    change p.instructions.mapM (ResolvedInstruction.matrix p.wireCount snapshot) = .ok matrices at hm
    exact ⟨wordMatrix matrices, by
      simp [ResolvedProgram.matrix, hm, Bind.bind, Except.bind, Pure.pure, Except.pure], hu⟩
  intro steps
  induction steps with
  | nil => exact fun _ => ⟨[], rfl, (unitaryGroup _ _).one_mem⟩
  | cons step tail ih =>
    simp only [List.all_cons, Bool.and_eq_true]
    rintro ⟨ok, ht⟩
    obtain ⟨u, hm⟩ := step.gateMatrix_exists snapshot ok
    obtain ⟨matrices, hr, hR⟩ := ih ht
    refine ⟨u :: matrices, ?_, (unitaryGroup _ _).mul_mem hR (step.gateMatrix_unitary snapshot ok hm)⟩
    simp [List.mapM_cons, hm, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A physical encoding frame places each logical input at its chosen basis state. -/
noncomputable def basisFrame {H I : Type} (embed : I ↪ H) : Matrix H I ℂ :=
  fun row col => if row = embed col then 1 else 0

theorem basisFrame_compress {H I : Type} [Fintype H] [DecidableEq H]
    (embed : I ↪ H) (u : Matrix H H ℂ) (row col : I) :
    compress (basisFrame embed) u (basisFrame embed) row col = u (embed row) (embed col) := by
  rw [compress, Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, basisFrame, mul_ite, ite_mul]

theorem basisFrame_isIsometry {H I : Type} [Fintype H] [DecidableEq H] [DecidableEq I]
    (embed : I ↪ H) : IsIsometry (basisFrame embed) := by
  ext row col
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, basisFrame, Matrix.one_apply,
    mul_ite, embed.injective.eq_iff, eq_comm]

end OracqVerify.RIR
