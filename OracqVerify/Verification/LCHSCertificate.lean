module

public import OracqVerify.RIR.RationalUnitary
public import OracqVerify.Verification.LCHSFixture

/-! A numerical certificate for the decoded Taylor branch at the first LCHS node. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.LCHS

open RIR Matrix
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.QspSimulation.Achievability
open scoped Matrix.Norms.L2Operator

private def loweredBranch : List (GateAction 7) :=
  (firstBranchTrace.instructions.mapM (GateAction.lower 7 false)).toOption.getD []

private theorem lower_branch :
    firstBranchTrace.instructions.mapM (GateAction.lower firstBranchTrace.wireCount false) =
      .ok loweredBranch := by rfl

attribute [local semireducible] Rat.mul Rat.inv Rat.add Rat.sub

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
private theorem branch_actions_supported : loweredBranch.all GateAction.approxSupported = true :=
  by decide +kernel

private theorem branch_actions_length : loweredBranch.length = 42 := rfl

private def rationalBranchColumn (col : Bool) : Reg 7 → Gaussian :=
  GateAction.runRational loweredBranch (rationalKet (zeroSignal 6 col))

private def rationalBranchEntry (row col : Bool) : Gaussian :=
  rationalBranchColumn col (zeroSignal 6 row)

private def taylorEntry (row col : Bool) : Gaussian :=
  if row = col then
    if row then ⟨2043 / 2048, 1 / 16⟩ else ⟨2011 / 2048, 3 / 16⟩
  else ⟨1 / 256, -(1 / 32)⟩

private theorem taylorEntry_exact (row col : Bool) :
    gaussianComplex (taylorEntry row col) = firstBranchTaylor row col := by
  rw [firstBranchTaylor, aeval_exponentialTaylorPolynomial]
  apply Complex.ext <;> cases row <;> cases col <;>
    norm_num [taylorEntry, Finset.sum_range_succ, firstBranchHamiltonian, firstBranchCoefficients,
      firstBranchTerms, Fin.sum_univ_three, Fintype.sum_bool, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, pow_two, PauliX, PauliZ, permMatrix, Complex.mul_re,
      Complex.mul_im]

private def scaledEntryDiscrepancy (row col : Bool) : Gaussian :=
  taylorEntry row col - (⟨2545 / 2048, 0⟩ : Gaussian) * rationalBranchEntry row col

private def columnCheck (col : Bool) : Bool :=
  let column := rationalBranchColumn col
  [false, true].all fun row =>
    let discrepancy := taylorEntry row col - (⟨2545 / 2048, 0⟩ : Gaussian) * column (zeroSignal 6 row)
    decide (|discrepancy.re| + |discrepancy.im| ≤ (1 : ℚ) / 10^12)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
private theorem columnsChecked (col : Bool) : columnCheck col = true := by
  cases col <;> decide +kernel

private theorem discrepancy_check (row col : Bool) :
    |(scaledEntryDiscrepancy row col).re| + |(scaledEntryDiscrepancy row col).im| ≤
      (1 : ℚ) / 10^12 := by
  have h := List.all_eq_true.mp (columnsChecked col) row (by cases row <;> simp)
  exact of_decide_eq_true h

private theorem discrepancy_norm (row col : Bool) :
    ‖firstBranchTaylor row col -
      ((firstBranchScale : ℝ) : ℂ) * gaussianComplex (rationalBranchEntry row col)‖ ≤
      (1 : ℝ) / 10^12 := by
  have hd := (Rat.cast_le (K := ℝ)).mpr (discrepancy_check row col)
  push_cast at hd
  have h := (Complex.norm_le_abs_re_add_abs_im
    (gaussianComplex (scaledEntryDiscrepancy row col))).trans hd
  simpa [scaledEntryDiscrepancy, gaussianComplex_real, taylorEntry_exact, firstBranchScale] using h

private theorem rationalBranchEntry_error {u : WireMatrix 7}
    (hm : firstBranchTrace.matrix (fun _ => none) = .ok u) (row col : Bool) :
    ‖u (zeroSignal 6 row) (zeroSignal 6 col) -
      gaussianComplex (rationalBranchEntry row col)‖ ≤ 2 * coefficientError * (4^42 - 2^42) := by
  have hu := GateAction.resolved_matrix (fun _ => none) lower_branch
  rw [hm] at hu
  have heq : u = wordMatrix (loweredBranch.map GateAction.matrix) := Except.ok.inj hu
  have hExact := GateAction.run_exact loweredBranch (Ket (zeroSignal 6 col))
  rw [← heq] at hExact
  have h := GateAction.run_approx loweredBranch branch_actions_supported (Ket (zeroSignal 6 col))
    (rationalKet (zeroSignal 6 col)) le_rfl le_rfl
    (fun r => by by_cases h : r = zeroSignal 6 col <;> simp [Ket, h])
    (fun r => by simp [rationalKet_value])
    (zeroSignal 6 row)
  rw [hExact, applyGate_eq_mulVec_ket, branch_actions_length] at h
  simpa [rationalBranchEntry, rationalBranchColumn, GateAction.runRational_eq] using h

private theorem entry_error {u : WireMatrix 7}
    (hm : firstBranchTrace.matrix (fun _ => none) = .ok u) (row col : Bool) :
    ‖(firstBranchTaylor - firstBranchBlock u) row col‖ ≤ (2 : ℝ) / 10^12 := by
  simp only [firstBranchBlock]
  have ha := discrepancy_norm row col
  have hb := rationalBranchEntry_error hm row col
  let p := firstBranchTaylor row col
  let q := gaussianComplex (rationalBranchEntry row col)
  let c := u (zeroSignal 6 row) (zeroSignal 6 col)
  let s : ℂ := firstBranchScale
  calc
    ‖p - s * c‖ = ‖(p - s * q) + s * (q - c)‖ := by ring_nf
    _ ≤ ‖p - s * q‖ + ‖s‖ * ‖c - q‖ := by
      simpa only [norm_mul, norm_sub_rev q c] using norm_add_le (p - s * q) (s * (q - c))
    _ ≤ (1 : ℝ) / 10^12 + ‖s‖ * (2 * coefficientError * (4^42 - 2^42)) :=
      add_le_add ha (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ ≤ _ := by norm_num [s, firstBranchScale, Complex.norm_real, coefficientError]

/-- The decoded first branch implements the degree-two Taylor polynomial with a proved
operator-norm discrepancy of at most `10⁻¹¹` in its scaled success block. -/
theorem firstBranch_polynomial_error {u : WireMatrix 7}
    (hm : firstBranchTrace.matrix (fun _ => none) = .ok u) :
    ‖firstBranchTaylor - firstBranchBlock u‖ ≤ (1 : ℝ) / 10^11 := by
  exact (norm_bool_matrix_le _ (by positivity) (entry_error hm)).trans (by norm_num)

/-- Discharge the numerical premise of the existing Taylor evolution contract for this artifact. -/
theorem firstBranch_certified_evolution :
    ∃ u : WireMatrix 7, firstBranchTrace.matrix (fun _ => none) = .ok u ∧
      BlockEncoding (hamiltonianEvolution firstBranchHamiltonian (1 / 8)) u
        (basisFrame (zeroSignal 6)) (basisFrame (zeroSignal 6)) firstBranchScale
        ((1 : ℝ) / 10^11 + 1 / 3) := by
  obtain ⟨u, hu, _⟩ := firstBranch_matrix
  exact ⟨u, hu, firstBranch_evolution hu (firstBranch_polynomial_error hu)⟩

end OracqVerify.Verification.LCHS
