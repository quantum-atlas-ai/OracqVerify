module

public import OracqVerify.Verification.LCHSFullArithmetic
public import OracqVerify.Verification.LCHSAssembled
public import Qatlib.Concepts.BlockEncoding.Postselection
import Mathlib.Analysis.Real.Pi.Bounds

/-! A certificate for both columns of the complete four-node LCHS success block. -/

set_option warningAsError true
set_option maxRecDepth 8000

public section

namespace OracqVerify.Verification.LCHS

open RIR Matrix Polynomial
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs
open scoped Matrix.Norms.L2Operator

private theorem actions_lowered :
    artifactTrace.instructions.mapM (GateAction.lower artifactTrace.wireCount false) =
      .ok artifactActions := rfl

private theorem actions_count : artifactActions.length = 155 := rfl

attribute [local semireducible] Rat.mul Rat.inv Rat.add Rat.sub

set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
private theorem actions_supported : artifactActions.all GateAction.approxSupported = true := by
  decide +kernel

private theorem actions_unitary : ∀ action ∈ artifactActions, action.matrix ∈ unitaryGroup (Reg 9) ℂ := by
  apply GateAction.lower_unitary _ actions_lowered
  decide

set_option maxHeartbeats 4000000 in
theorem numerator_exact (row col : Bool) :
    (Real.pi : ℂ) * artifactTaylor row col = gaussianComplex (taylorNumerator row col) := by
  have weight (j : Fin 4) : (Real.pi : ℂ) * staticLchsCoeff 1 4 j =
      Complex.ofReal ((1 / 2) / (1 + (staticLchsGrid 1 4 j) ^ 2)) := by
    rw [staticLchsCoeff, ← Complex.ofReal_mul]
    congr 1
    have hp : 1 + (staticLchsGrid 1 4 j) ^ 2 ≠ 0 := by positivity
    field_simp [Real.pi_ne_zero, hp]
    ring
  unfold artifactTaylor
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc, weight]
  apply Complex.ext <;> cases row <;> cases col <;>
    norm_num [taylorNumerator, Fin.sum_univ_four, aeval_exponentialTaylorPolynomial, staticLchsGrid,
      Finset.sum_range_succ, sampleH, sampleL, Fintype.sum_bool, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, pow_two, PauliX, permMatrix, Complex.mul_re, Complex.mul_im]

private theorem unitary_error_budget : (155 : ℝ) * unitaryRoundError 9 ≤ 1 / 10^25 := by
  norm_num [unitaryRoundError, Reg, Fintype.card_fun, coefficientError]

private theorem rationalEntry_error {u : WireMatrix 9}
    (hm : artifactTrace.matrix (fun _ => none) = .ok u) (row col : Bool) :
    ‖u (zeroSignal 8 row) (zeroSignal 8 col) -
      gaussianComplex (artifactRationalColumn col (zeroSignal 8 row))‖ ≤ (1 : ℝ) / 10^25 := by
  have hu := GateAction.resolved_matrix (fun _ => none) actions_lowered
  rw [hm] at hu
  have heq : u = wordMatrix (artifactActions.map GateAction.matrix) := Except.ok.inj hu
  let input := Ket (zeroSignal 8 col)
  have hr : gaussianComplex ∘ rationalKet (zeroSignal 8 col) = input :=
    funext (rationalKet_value _)
  have hNorm : ‖toEuclidean_fromVec input‖ ≤ 1 :=
    ((normalized_iff_norm_toEuclidean_fromVec input).mp (normalized_ket _)).le
  have hBudget : (0 : ℝ) + artifactActions.length * unitaryRoundError 9 ≤ 1 := by
    rw [zero_add, actions_count]
    exact unitary_error_budget.trans (by norm_num)
  have approx := GateAction.run_approx_unitary artifactActions actions_supported actions_unitary input
    (rationalKet (zeroSignal 8 col)) 0 hNorm (by
      rw [hr, sub_self]
      have hz : toEuclidean_fromVec (0 : QState (Reg 9)) = 0 := by ext i; simp
      rw [hz, norm_zero]) hBudget
  rw [GateAction.run_exact, ← heq, zero_add, actions_count] at approx
  have hCoordinate := (PiLp.norm_apply_le (toEuclidean_fromVec _) (zeroSignal 8 row)).trans approx
  simpa [input, artifactRationalColumn, GateAction.runRational_eq, applyGate_eq_mulVec_ket] using
    hCoordinate.trans unitary_error_budget

private theorem entry_error_full {u : WireMatrix 9}
    (hm : artifactTrace.matrix (fun _ => none) = .ok u) (row col : Bool) :
    ‖(artifactTaylor - artifactSuccessBlock u) row col‖ ≤ (1 : ℝ) / 10^12 := by
  let A := artifactTaylor row col
  let U := u (zeroSignal 8 row) (zeroSignal 8 col)
  let R := gaussianComplex (artifactRationalColumn col (zeroSignal 8 row))
  let a : ℂ := (artifactScale : ℂ)
  let p : ℂ := ((rationalPiLower : ℝ) : ℂ)
  obtain ⟨v, hv, hu⟩ := artifact_matrix
  rw [hm] at hv
  cases hv
  have hU : ‖U‖ ≤ 1 := entry_norm_bound_of_unitary hu _ _
  have hR : ‖R - U‖ ≤ (1 : ℝ) / 10^25 := by
    rw [norm_sub_rev]
    exact rationalEntry_error hm row col
  have ha : ‖a‖ ≤ 1 := by norm_num [a, artifactScale, Complex.norm_real, Real.norm_eq_abs]
  have hp : ‖p‖ ≤ 4 := by norm_num [p, rationalPiLower, Complex.norm_real, Real.norm_eq_abs]
  have hpi : ‖p - (Real.pi : ℂ)‖ ≤ 1 / 10^20 := by
    change ‖((rationalPiLower : ℝ) : ℂ) - (Real.pi : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have lo := Real.pi_gt_d20
    have hi := Real.pi_lt_d20
    norm_num [rationalPiLower] at lo hi ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hChecked : ‖(Real.pi : ℂ) * A - p * a * R‖ ≤ (1 : ℝ) / 10^12 := by
    change ‖(Real.pi : ℂ) * artifactTaylor row col - p * a * R‖ ≤ _
    rw [numerator_exact]
    have hd := (Rat.cast_le (K := ℝ)).mpr (checked_columns row col)
    push_cast at hd
    have hNorm := (Complex.norm_le_abs_re_add_abs_im (gaussianComplex
      (artifactEntryDiscrepancy row col (artifactRationalColumn col (zeroSignal 8 row))))).trans hd
    simpa [artifactEntryDiscrepancy, gaussianComplex_real, p, a, R, artifactRationalScale, artifactScale, Rat.cast_mul]
      using hNorm
  have hScaled : ‖(Real.pi : ℂ) * (A - a * U)‖ ≤ (2 : ℝ) / 10^12 := by
    rw [show (Real.pi : ℂ) * (A - a * U) =
      ((Real.pi : ℂ) * A - p * a * R) + p * a * (R - U) + (p - (Real.pi : ℂ)) * a * U by ring]
    have h₁ : ‖p * a * (R - U)‖ ≤ 4 * (1 : ℝ) / 10^25 := by
      simp only [norm_mul]
      calc
        _ ≤ (4 : ℝ) * 1 * (1 / 10^25) := by gcongr
        _ = (4 : ℝ) * 1 / 10^25 := by ring
    have h₂ : ‖(p - (Real.pi : ℂ)) * a * U‖ ≤ (1 : ℝ) / 10^20 := by
      simp only [norm_mul]
      calc
        _ ≤ ((1 : ℝ) / 10^20) * 1 * 1 := by gcongr
        _ = (1 : ℝ) / 10^20 := by ring
    exact ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hChecked h₁)) h₂)).trans
      (by norm_num)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hScaled
  change ‖A - a * U‖ ≤ _
  have hπ : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  nlinarith [mul_le_mul_of_nonneg_right hπ (norm_nonneg (A - a * U))]

/-- The complete serialized success block implements the Cauchy-weighted Taylor sum. -/
theorem artifact_polynomial_error {u : WireMatrix 9}
    (hm : artifactTrace.matrix (fun _ => none) = .ok u) :
    ‖artifactTaylor - artifactSuccessBlock u‖ ≤ (1 : ℝ) / 10^11 :=
  (norm_bool_matrix_le _ (by positivity) (entry_error_full hm)).trans (by norm_num)

/-- The fixture exercises the noncommuting case of the static algorithm. -/
theorem sample_noncommuting : sampleL * sampleH ≠ sampleH * sampleL := by
  intro commutes
  have h := congrArg (fun m : Matrix Bool Bool ℂ => m false true) commutes
  norm_num [sampleL, sampleH, PauliX, permMatrix, Matrix.mul_apply, Matrix.smul_apply,
    Complex.real_smul, Fintype.sum_bool] at h

/-- An end-to-end error bound for the success block of the generated nine-wire program. -/
theorem artifact_certified_evolution :
    ∃ u : WireMatrix 9, artifactTrace.matrix (fun _ => none) = .ok u ∧
      BlockEncoding (staticNonunitaryEvolution sampleL sampleH (1 / 8)) u
        (basisFrame (zeroSignal 8)) (basisFrame (zeroSignal 8)) artifactScale
        (quadratureError sampleL (1 / 8) 1 4 + artifactTaylorError + (1 : ℝ) / 10^11) := by
  obtain ⟨u, hu, _⟩ := artifact_matrix
  exact ⟨u, hu, assembled_evolution hu (artifact_polynomial_error hu)⟩

/-- The all-zero signal outcome has substantial probability on the fixture's prepared input. -/
theorem artifact_zero_success_probability {u : WireMatrix 9}
    (hm : artifactTrace.matrix (fun _ => none) = .ok u) :
    (36 : ℝ) / 49 ≤ postselectionProbability u
      (basisFrame (zeroSignal 8)) (basisFrame (zeroSignal 8)) (Ket false) := by
  let P := artifactTaylor false false
  let U := u (zeroSignal 8 false) (zeroSignal 8 false)
  have hπ : Real.pi * P.re = (63133 : ℝ) / 40960 := by
    have h := congrArg Complex.re (numerator_exact false false)
    simpa [P, Complex.mul_re, taylorNumerator] using h
  have hP : (39 : ℝ) / 80 ≤ P.re := by
    by_contra not_le
    have h := mul_le_mul_of_nonneg_left (le_of_not_ge not_le) Real.pi_pos.le
    have h' := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (by norm_num : 0 ≤ (39 : ℝ) / 80)
    linarith
  have hErr := entry_error_full hm false false
  change ‖P - (artifactScale : ℂ) * U‖ ≤ (1 : ℝ) / 10^12 at hErr
  have hRe := (Complex.abs_re_le_norm (P - (artifactScale : ℂ) * U)).trans hErr
  rw [Complex.sub_re] at hRe
  have h₁ := (le_abs_self _).trans hRe
  have h₂ := Complex.re_le_norm ((artifactScale : ℂ) * U)
  have hScaleNonneg : 0 ≤ artifactScale := by norm_num [artifactScale]
  have hScale : artifactScale ≤ (9 : ℝ) / 16 := by norm_num [artifactScale]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScaleNonneg] at h₂
  have h₃ := mul_le_mul_of_nonneg_right hScale (norm_nonneg U)
  have hAmplitude : (6 : ℝ) / 7 ≤ ‖U‖ := by linarith
  let frame := basisFrame (zeroSignal 8)
  let output := postselectionVector u frame frame (Ket false)
  have hCol : output false = U := by
    change ApplyGate (compress frame u frame) (Ket false) false = _
    rw [applyGate_eq_mulVec_ket]
    exact basisFrame_compress (zeroSignal 8) u false false
  have hNorm := PiLp.norm_apply_le (stateVector output) false
  change ‖output false‖ ≤ ‖stateVector output‖ at hNorm
  rw [hCol] at hNorm
  have hSquare := (sq_le_sq₀ (by norm_num : 0 ≤ (6 : ℝ) / 7) (norm_nonneg _)).mpr
    (hAmplitude.trans hNorm)
  rw [postselectionProbability_eq_norm_sq (basisFrame_isIsometry _)]
  convert hSquare using 1
  norm_num

end OracqVerify.Verification.LCHS
