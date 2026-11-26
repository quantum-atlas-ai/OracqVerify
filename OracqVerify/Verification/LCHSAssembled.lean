module

public import OracqVerify.Verification.LCHSFixture

/-! Transfer an error certificate for the full physical success block directly to LCHS. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.LCHS

open RIR Matrix Polynomial
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.FactorialTaylor Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LchsSimulation.StaticLchs
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Retain the size of the exponent in the factorial Taylor tail bound. -/
theorem taylorRemainder {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) (n : Nat) (θ : ℝ) (hθ : θ ≤ 1)
    (hNorm : ‖((-Complex.I * (t : ℂ)) • A : Matrix I I ℂ)‖ ≤ θ) :
    ‖aeval A (exponentialTaylorPolynomial t (n + 1)) - hamiltonianEvolution A t‖ ≤
      2 * θ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  let X : Matrix I I ℂ := (-Complex.I * (t : ℂ)) • A
  let f : Nat → Matrix I I ℂ := fun k => (k.factorial : ℂ)⁻¹ • X ^ k
  have hθ₀ : 0 ≤ θ := (norm_nonneg _).trans hNorm
  have hf : Summable f := NormedSpace.expSeries_summable' X
  have hfn : Summable fun k => ‖f k‖ := NormedSpace.norm_expSeries_summable' X
  have ht : ∑' k, f k = NormedSpace.exp X := (NormedSpace.exp_series_hasSum_exp' X).tsum_eq
  have htail : NormedSpace.exp X - ∑ k ∈ Finset.range (n + 1), f k =
      ∑' k, f (k + (n + 1)) := by
    have hs := hf.sum_add_tsum_nat_add (n + 1)
    rw [ht] at hs
    exact (eq_sub_of_add_eq' hs).symm
  have hterm (k : Nat) (hk : 0 < k) : ‖f k‖ ≤ θ ^ k / (k.factorial : ℝ) := by
    calc
      ‖f k‖ = (k.factorial : ℝ)⁻¹ * ‖X ^ k‖ := by simp [f, norm_smul, norm_inv]
      _ ≤ (k.factorial : ℝ)⁻¹ * ‖X‖ ^ k :=
        mul_le_mul_of_nonneg_left (norm_pow_le' X hk) (by positivity)
      _ ≤ (k.factorial : ℝ)⁻¹ * θ ^ k := by gcongr
      _ = θ ^ k / (k.factorial : ℝ) := by rw [div_eq_mul_inv, mul_comm]
  have hn : Summable fun k => ‖f (k + (n + 1))‖ := (summable_nat_add_iff _).2 hfn
  have hs := factorial_taylor_tail_and_coherent_precision.1 θ n hθ₀ hθ
  have hg : Summable fun k : Nat => θ ^ (k + (n + 1)) / ((k + (n + 1)).factorial : ℝ) := by
    simpa [Nat.add_comm] using! hs.1
  rw [aeval_exponentialTaylorPolynomial, norm_sub_rev]
  change ‖NormedSpace.exp X - ∑ k ∈ Finset.range (n + 1), f k‖ ≤ _
  rw [htail]
  calc
    ‖∑' k, f (k + (n + 1))‖ ≤ ∑' k, ‖f (k + (n + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, θ ^ (k + (n + 1)) / ((k + (n + 1)).factorial : ℝ) :=
      hn.tsum_le_tsum (fun k => hterm _ (by omega)) hg
    _ ≤ 2 * θ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      simpa [Nat.add_comm] using! hs.2

/-- The weighted polynomial implemented by the four-node circuit before its analytic errors. -/
@[expose] noncomputable def artifactTaylor : Matrix Bool Bool ℂ :=
  ∑ j : Fin 4, staticLchsCoeff 1 4 j •
    aeval (sampleH + staticLchsGrid 1 4 j • sampleL) (exponentialTaylorPolynomial (1 / 8) 3)

theorem sampleL_norm_le : ‖sampleL‖ ≤ (3 : ℝ) / 2 := by
  unfold sampleL
  rw [l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro bit
  cases bit <;> norm_num [Complex.norm_div, Complex.norm_natCast]

theorem sampleH_norm_le : ‖sampleH‖ ≤ (1 : ℝ) / 4 := by
  unfold sampleH
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ) / 4)]
  exact mul_le_of_le_one_right (by norm_num) (l2_norm_unitary_le_one pauliX_unitary)

private theorem grid_abs_le (j : Fin 4) : |staticLchsGrid 1 4 j| ≤ 1 := by
  fin_cases j <;> norm_num [staticLchsGrid]

theorem artifact_nodeTaylor (j : Fin 4) :
    ‖aeval (sampleH + staticLchsGrid 1 4 j • sampleL) (exponentialTaylorPolynomial (1 / 8) 3) -
      hamiltonianEvolution (sampleH + staticLchsGrid 1 4 j • sampleL) (1 / 8)‖ ≤
      2 * ((7 : ℝ) / 32) ^ 3 / 6 := by
  have hH : ‖sampleH + staticLchsGrid 1 4 j • sampleL‖ ≤ (7 : ℝ) / 4 := by
    refine (norm_add_le ..).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have hs := mul_le_mul (grid_abs_le j) sampleL_norm_le (norm_nonneg _) zero_le_one
    linarith [sampleH_norm_le, hs]
  have hn : ‖((-Complex.I * ((1 / 8 : ℝ) : ℂ)) •
      (sampleH + staticLchsGrid 1 4 j • sampleL))‖ ≤ (7 : ℝ) / 32 := by
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num only [show |(1 : ℝ) / 8| = 1 / 8 by norm_num]
    linarith
  have h := taylorRemainder _ (1 / 8) 2 (7 / 32) (by norm_num) hn
  simpa [Nat.factorial] using h

@[expose] noncomputable def artifactTaylorError : ℝ :=
  (∑ j : Fin 4, ‖staticLchsCoeff 1 4 j‖) * (2 * ((7 : ℝ) / 32) ^ 3 / 6)

theorem artifactTaylor_quadrature :
    ‖artifactTaylor - staticLchsQuadrature sampleL sampleH (1 / 8) 1 4‖ ≤ artifactTaylorError := by
  unfold artifactTaylor staticLchsQuadrature artifactTaylorError
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left (artifact_nodeTaylor j) (norm_nonneg _)

theorem artifactTaylor_error : ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor‖ ≤
    quadratureError sampleL (1 / 8) 1 4 + artifactTaylorError := by
  let ideal := staticLchsQuadrature sampleL sampleH (1 / 8) 1 4
  have hQ := static_noncommuting_lchs_quadrature_error Bool sampleL sampleH (1 / 8) 1 4
    sampleL_posSemidef sampleH_hermitian (by norm_num) (by decide) (by decide)
  calc
    _ = ‖(staticNonunitaryEvolution sampleL sampleH (1 / 8) - ideal) +
        (ideal - artifactTaylor)‖ := by congr 1; abel
    _ ≤ _ := by
      refine (norm_add_le ..).trans ?_
      rw [norm_sub_rev _ ideal, norm_sub_rev ideal artifactTaylor]
      exact add_le_add hQ artifactTaylor_quadrature

/-- The entry's decimal normalization, checked when loading the fixture. -/
@[expose] noncomputable def artifactScale : ℝ := 551563578415394 / 10^15

@[expose] noncomputable def artifactSuccessBlock (u : WireMatrix 9) : Matrix Bool Bool ℂ :=
  artifactScale • (fun row col => u (zeroSignal 8 row) (zeroSignal 8 col))

/-- A single bound on the full compressed circuit suffices to certify the approximation. -/
theorem assembled_evolution {u : WireMatrix 9} {δ : ℝ}
    (hm : artifactTrace.matrix (fun _ => none) = .ok u)
    (hδ : ‖artifactTaylor - artifactSuccessBlock u‖ ≤ δ) :
    BlockEncoding (staticNonunitaryEvolution sampleL sampleH (1 / 8)) u
      (basisFrame (zeroSignal 8)) (basisFrame (zeroSignal 8)) artifactScale
      (quadratureError sampleL (1 / 8) 1 4 + artifactTaylorError + δ) := by
  obtain ⟨v, hv, hu⟩ := artifact_matrix
  rw [hm] at hv
  cases hv
  have hExact : BlockEncoding (artifactSuccessBlock u) u
      (basisFrame (zeroSignal 8)) (basisFrame (zeroSignal 8)) artifactScale 0 := by
    refine ⟨hu, basisFrame_isIsometry _, basisFrame_isIsometry _,
      by norm_num [artifactScale], le_rfl, ?_⟩
    have hc : compress (basisFrame (zeroSignal 8)) u (basisFrame (zeroSignal 8)) =
        (fun row col => u (zeroSignal 8 row) (zeroSignal 8 col)) := by
      ext row col
      exact basisFrame_compress (zeroSignal 8) u row col
    have hs : artifactSuccessBlock u = artifactScale •
        compress (basisFrame (zeroSignal 8)) u (basisFrame (zeroSignal 8)) :=
      congrArg (artifactScale • ·) hc.symm
    rw [← hs, sub_self, norm_zero]
  have hb : ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactSuccessBlock u‖ ≤
      quadratureError sampleL (1 / 8) 1 4 + artifactTaylorError + δ := by
    rw [show staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactSuccessBlock u =
        (staticNonunitaryEvolution sampleL sampleH (1 / 8) - artifactTaylor) +
          (artifactTaylor - artifactSuccessBlock u) by abel]
    exact (norm_add_le ..).trans (add_le_add artifactTaylor_error hδ)
  simpa only [zero_add] using hExact.perturb ((norm_nonneg _).trans hb) hb

end OracqVerify.Verification.LCHS
