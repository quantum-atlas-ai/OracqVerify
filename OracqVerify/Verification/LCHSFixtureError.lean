module

public import OracqVerify.Verification.LCHSFullCertificate
import Mathlib.Analysis.Real.Pi.Bounds

/-! Instance-specific error bounds for the coarse four-node quadrature and its circuit. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.LCHS

open RIR Matrix Polynomial Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Concepts.QspSimulation.Achievability
open scoped Matrix.Norms.L2Operator

private noncomputable def evolutionHamiltonian : Matrix Bool Bool ℂ :=
  sampleH - Complex.I • sampleL

noncomputable def evolutionTaylor : Matrix Bool Bool ℂ :=
  aeval evolutionHamiltonian (exponentialTaylorPolynomial (1 / 8) 3)

private theorem evolution_eq : hamiltonianEvolution evolutionHamiltonian (1 / 8) =
    staticNonunitaryEvolution sampleL sampleH (1 / 8) := by
  unfold hamiltonianEvolution staticNonunitaryEvolution evolutionHamiltonian
  congr 1
  rw [← Complex.coe_smul]
  ext row col
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply]
  push_cast
  linear_combination ((1 : ℂ) / 8 * sampleL row col) * Complex.I_sq

theorem evolutionTaylor_remainder :
    ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - evolutionTaylor‖ ≤ (343 : ℝ) / 98304 := by
  have h : ‖evolutionHamiltonian‖ ≤ (7 : ℝ) / 4 := by
    unfold evolutionHamiltonian
    refine (norm_sub_le ..).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith [sampleH_norm_le, sampleL_norm_le]
  have hScale : ‖(-Complex.I * (((1 : ℝ) / 8 : ℝ) : ℂ)) • evolutionHamiltonian‖ ≤
      (7 : ℝ) / 32 := by
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num only [show |(1 : ℝ) / 8| = 1 / 8 by norm_num]
    linarith
  rw [← evolution_eq, norm_sub_rev]
  unfold evolutionTaylor
  refine (taylorRemainder evolutionHamiltonian (1 / 8) 2 (7 / 32) (by norm_num) hScale).trans ?_
  norm_num [Nat.factorial]

@[expose] def evolutionEntry (row col : Bool) : Gaussian :=
  if row = col then ⟨if row then 1923 / 2048 else 1699 / 2048, 0⟩ else ⟨0, -(7 / 256)⟩

theorem evolutionTaylor_entry (row col : Bool) :
    evolutionTaylor row col = gaussianComplex (evolutionEntry row col) := by
  simp only [evolutionTaylor, aeval_exponentialTaylorPolynomial]
  apply Complex.ext <;> cases row <;> cases col <;>
    norm_num [evolutionEntry, evolutionHamiltonian, Finset.sum_range_succ, Fintype.sum_bool,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply,
      sampleH, sampleL, PauliX, permMatrix, pow_two, Complex.mul_re, Complex.mul_im]

private theorem artifactTaylor_entry (row col : Bool) :
    artifactTaylor row col = ((Real.pi⁻¹ : ℝ) : ℂ) * gaussianComplex (taylorNumerator row col) := by
  rw [← numerator_exact, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ Real.pi_ne_zero,
    Complex.ofReal_one, one_mul]

private theorem invPi_bounds : (159 : ℝ) / 500 ≤ Real.pi⁻¹ ∧ Real.pi⁻¹ ≤ (319 : ℝ) / 1000 := by
  rw [← one_div]
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_d4]
  · apply (div_le_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_d2]

private theorem entryGap (row col : Bool) :
    ‖(evolutionTaylor - artifactTaylor) row col‖ ≤
      if row = col then (452 : ℝ) / 1000 else 13 / 1000 := by
  obtain ⟨lo, hi⟩ := invPi_bounds
  rw [Matrix.sub_apply, evolutionTaylor_entry, artifactTaylor_entry]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  cases row <;> cases col <;>
    norm_num [evolutionEntry, taylorNumerator, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
  all_goals
    rw [abs_eq_max_neg, max_def]
    split <;> linarith

/-- Bound the diagonal and off-diagonal parts separately in operator norm. -/
theorem boolMatrixNorm (A : Matrix Bool Bool ℂ) {diag off : ℝ} (hd : 0 ≤ diag) (ho : 0 ≤ off)
    (hDiag : ∀ i, ‖A i i‖ ≤ diag) (hOff : ∀ i, ‖A i (!i)‖ ≤ off) : ‖A‖ ≤ diag + off := by
  let D := Matrix.diagonal fun i => A i i
  let O := Matrix.diagonal fun i => A i (!i)
  have h : A = D + O * PauliX := by
    ext i j
    cases i <;> cases j <;> simp [D, O, PauliX, permMatrix, Matrix.diagonal_mul]
  have hD : ‖D‖ ≤ diag := by
    rw [l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hd]
    exact hDiag
  have hO : ‖O‖ ≤ off := by
    rw [l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg ho]
    exact hOff
  rw [h]
  refine (norm_add_le ..).trans (add_le_add hD ?_)
  exact (norm_mul_le O _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (l2_norm_unitary_le_one pauliX_unitary)).trans hO)

private theorem evolutionTaylor_gap : ‖evolutionTaylor - artifactTaylor‖ ≤ (465 : ℝ) / 1000 := by
  have h := boolMatrixNorm (evolutionTaylor - artifactTaylor) (diag := 452 / 1000) (off := 13 / 1000)
    (by norm_num) (by norm_num) (fun i => by simpa using entryGap i i)
    (fun i => by
      cases i
      · simpa using entryGap false true
      · simpa using entryGap true false)
  convert h using 1
  norm_num

private theorem evolution_to_artifactTaylor :
    ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor‖ ≤
      (465 : ℝ) / 1000 + 343 / 98304 := by
  rw [show staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor =
      (evolutionTaylor - artifactTaylor) + (staticNonunitaryEvolution sampleL sampleH (1 / 8) - evolutionTaylor)
      by abel]
  exact (norm_add_le ..).trans (add_le_add evolutionTaylor_gap evolutionTaylor_remainder)

theorem weight_mass_le : (∑ j : Fin 4, ‖staticLchsCoeff 1 4 j‖) ≤ (1 : ℝ) := by
  have bound (j : Fin 4) : ‖staticLchsCoeff 1 4 j‖ ≤ (1 : ℝ) / 4 := by
    rw [staticLchsCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity)).2
    have h : Real.pi * 1 ≤ Real.pi * (1 + staticLchsGrid 1 4 j ^ 2) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg (staticLchsGrid 1 4 j))) Real.pi_pos.le
    linarith [Real.pi_gt_d2]
  calc
    _ ≤ ∑ _ : Fin 4, (1 : ℝ) / 4 := Finset.sum_le_sum fun j _ => bound j
    _ = 1 := by norm_num

/-- At the fixture's four nodes the exact finite quadrature is within 0.48 of the continuum evolution. -/
theorem artifact_quadrature_error :
    ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - staticLchsQuadrature sampleL sampleH (1 / 8) 1 4‖ ≤
      (12 : ℝ) / 25 := by
  have hTaylor : artifactTaylorError ≤ (343 : ℝ) / 98304 := by
    unfold artifactTaylorError
    exact (mul_le_mul_of_nonneg_right weight_mass_le (by positivity)).trans (by norm_num)
  rw [show staticNonunitaryEvolution sampleL sampleH (1 / 8) - staticLchsQuadrature sampleL sampleH (1 / 8) 1 4 =
      (staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor) +
      (artifactTaylor - staticLchsQuadrature sampleL sampleH (1 / 8) 1 4) by abel]
  exact ((norm_add_le ..).trans (add_le_add evolution_to_artifactTaylor
    (artifactTaylor_quadrature.trans hTaylor))).trans (by norm_num)

/-- The serialized circuit's scaled success block has at most 0.47 operator error on this instance. -/
theorem artifact_fixture_evolution :
    ∃ u : WireMatrix 9, artifactTrace.matrix (fun _ => none) = .ok u ∧
      BlockEncoding (staticNonunitaryEvolution sampleL sampleH (1 / 8)) u
        (basisFrame (zeroSignal 8)) (basisFrame (zeroSignal 8)) artifactScale ((47 : ℝ) / 100) := by
  obtain ⟨u, hu, encoding⟩ := artifact_certified_evolution
  refine ⟨u, hu, encoding.unitary, encoding.left_isometry, encoding.right_isometry,
    encoding.normalization_pos, by norm_num, ?_⟩
  have hc : artifactSuccessBlock u = artifactScale •
      compress (basisFrame (zeroSignal 8)) u (basisFrame (zeroSignal 8)) := by
    have hComp : compress (basisFrame (zeroSignal 8)) u (basisFrame (zeroSignal 8)) =
        (fun row col => u (zeroSignal 8 row) (zeroSignal 8 col)) := by
      ext row col
      exact basisFrame_compress (zeroSignal 8) u row col
    exact congrArg (artifactScale • ·) hComp.symm
  rw [← hc, show staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactSuccessBlock u =
      (staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor) +
      (artifactTaylor - artifactSuccessBlock u) by abel]
  exact ((norm_add_le ..).trans (add_le_add evolution_to_artifactTaylor
    (artifact_polynomial_error hu))).trans (by norm_num)

end OracqVerify.Verification.LCHS
