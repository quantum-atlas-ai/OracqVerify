module

public import Qatlib.Concepts.BlockEncoding.Postselection

/-! Stability of postselected block encodings under input preparation error. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

private theorem normalized_difference_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖y‖ * ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
  let u := NormedSpace.normalize y
  let v := NormedSpace.normalize x
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hy
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize hx
  have yScale : ‖y‖ • u = y := NormedSpace.norm_smul_normalize y
  have xScale : ‖x‖ • v = x := NormedSpace.norm_smul_normalize x
  have h :
      ‖y - x‖ ^ 2 =
        (‖y‖ - ‖x‖) ^ 2 + ‖x‖ * ‖y‖ * ‖u - v‖ ^ 2 := by
    calc
      _ = ‖‖y‖ • u - ‖x‖ • v‖ ^ 2 := by rw [yScale, xScale]
      _ = _ := by
        rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
          Real.norm_of_nonneg (norm_nonneg y), Real.norm_of_nonneg (norm_nonneg x), hu, hv,
          inner_smul_left, inner_smul_right]
        simp only [conj_trivial, mul_one]
        ring
  change ‖x‖ * ‖y‖ * ‖u - v‖ ^ 2 ≤ _
  rw [h]
  exact le_add_of_nonneg_left (sq_nonneg _)

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- A normalized approximate input to a reciprocal block encoding preserves the
success guarantee from the inverse's uniform lower norm bound. The output error
combines the block error with the input error amplified by the intended map. -/
theorem postselection_with_input_error {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε γ δ : ℝ}
    (encoding : BlockEncoding A U L R α ε)
    {actual ideal : QState I} (actualUnit : Normalized actual) (idealUnit : Normalized ideal)
    (inputError : ‖stateVector (actual - ideal)‖ ≤ δ)
    (lower : ∀ ψ : QState I, Normalized ψ → γ ≤ ‖stateVector (A *ᵥ ψ)‖)
    (gap : ε < γ) :
    ((γ - ε) / α) ^ 2 ≤ postselectionProbability U L R actual ∧
    0 < postselectionProbability U L R actual ∧
    ∃ φ, postselectionOutput U L R actual = some φ ∧
      IsNormalizedApplication A ideal φ
        ((ε + ‖A‖ * δ) / Real.sqrt (‖stateVector (A *ᵥ ideal)‖ * (γ - ε))) := by
  let x := stateVector (A *ᵥ ideal)
  let y := α • stateVector (postselectionVector U L R actual)
  have hε : 0 ≤ ε := encoding.error_nonneg
  have hγ : 0 < γ := hε.trans_lt gap
  have hδ : 0 ≤ δ := (norm_nonneg _).trans inputError
  have hx : γ ≤ ‖x‖ := lower ideal idealUnit
  have actualLower := lower actual actualUnit
  have hBlock := BlockEncoding.postselection_error encoding actualUnit
  have hy : γ - ε ≤ ‖y‖ := by
    have hTriangle := norm_sub_norm_le (stateVector (A *ᵥ actual)) y
    change ‖stateVector (A *ᵥ actual) - y‖ ≤ ε at hBlock
    linarith
  have hx' : x ≠ 0 := norm_pos_iff.mp (hγ.trans_le hx)
  have hy' : y ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr gap).trans_le hy)
  have hApply :
      ‖stateVector (A *ᵥ actual) - x‖ ≤ ‖A‖ * δ := by
    dsimp only [x]
    have hm := stateVector_mulVec_norm_le A (actual - ideal)
    rw [Matrix.mulVec_sub, show stateVector (A *ᵥ actual - A *ᵥ ideal) =
      stateVector (A *ᵥ actual) - stateVector (A *ᵥ ideal) from rfl] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left inputError (norm_nonneg A))
  have hClose : ‖y - x‖ ≤ ε + ‖A‖ * δ := by
    calc
      _ = ‖(y - stateVector (A *ᵥ actual)) + (stateVector (A *ᵥ actual) - x)‖ := by
        congr 1
        abel
      _ ≤ ‖y - stateVector (A *ᵥ actual)‖ + ‖stateVector (A *ᵥ actual) - x‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_sub_rev y]
        exact add_le_add hBlock hApply
  have hPos : 0 < ‖x‖ * (γ - ε) := mul_pos (hγ.trans_le hx) (sub_pos.mpr gap)
  have hState :
      ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤
        (ε + ‖A‖ * δ) / Real.sqrt (‖x‖ * (γ - ε)) := by
    let _ : InnerProductSpace ℝ (EuclideanSpace ℂ O) := InnerProductSpace.rclikeToReal ℂ _
    have hSq := normalized_difference_sq hx' hy'
    have hξ : 0 ≤ ε + ‖A‖ * δ := add_nonneg hε (mul_nonneg (norm_nonneg A) hδ)
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hPos)).mpr
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hξ).mp
    rw [mul_pow, Real.sq_sqrt hPos.le, mul_comm]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hy (norm_nonneg x)) (sq_nonneg _)).trans
      (hSq.trans (pow_le_pow_left₀ (norm_nonneg _) hClose 2))
  have hProb : ((γ - ε) / α) ^ 2 ≤ postselectionProbability U L R actual := by
    have bound := BlockEncoding.postselection_probability_lower encoding actualUnit
      (gap.le.trans actualLower)
    refine (pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr gap.le) encoding.normalization_pos.le) ?_ 2).trans bound
    exact div_le_div_of_nonneg_right (sub_le_sub_right actualLower _) encoding.normalization_pos.le
  have hSuccess : 0 < postselectionProbability U L R actual :=
    (pow_pos (div_pos (sub_pos.mpr gap) encoding.normalization_pos) _).trans_le hProb
  have nonzero : postselectionVector U L R actual ≠ 0 := by
    intro hz
    exact hy' (by simp [y, hz])
  have idealNonzero : A *ᵥ ideal ≠ 0 := by
    intro hz
    exact hx' (by simp [x, hz])
  have accepts : postselectionOutput U L R actual = some (PostMeasure (postselectionVector U L R actual) Finset.univ) :=
    conditionalState_eq_some_of_ne_zero nonzero
  refine ⟨hProb, hSuccess, _, accepts, idealNonzero, ?_, ?_⟩
  · exact normalized_of_conditionalState_eq_some (conditionalState_eq_some_of_ne_zero nonzero)
  · rw [stateVector_postMeasure_univ]
    simpa only [y, x, NormedSpace.normalize_smul_of_pos encoding.normalization_pos] using hState

end OracqVerify.RIR
