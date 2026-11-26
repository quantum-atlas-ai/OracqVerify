module

public import OracqVerify.RIR.RationalAction
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-! A linear error bound for the rational evaluator on checked unitary words. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Concepts.ReferenceError.RefTraceError
open scoped Matrix Matrix.Norms.L2Operator

private theorem amplitude_le {I : Type} [Fintype I] (state : QState I) (row : I) :
    ‖state row‖ ≤ ‖toEuclidean_fromVec state‖ :=
  PiLp.norm_apply_le (toEuclidean_fromVec state) row

private theorem euclidean_le_of_coordinates {I : Type} [Fintype I] [Nonempty I]
    (state : QState I) {e : ℝ} (he : 0 ≤ e) (h : ∀ row, ‖state row‖ ≤ e) :
    ‖toEuclidean_fromVec state‖ ≤ (Fintype.card I : ℝ) * e := by
  have hc : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toEuclidean_fromVec_sq]
  calc
    _ ≤ ∑ _ : I, e ^ 2 := Finset.sum_le_sum fun row _ =>
      (sq_le_sq₀ (norm_nonneg _) he).mpr (h row)
    _ = (Fintype.card I : ℝ) * e ^ 2 := by simp
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg e)]

/-- One rounding step injects at most this Euclidean error while the approximate norm is at most two. -/
@[expose] noncomputable def unitaryRoundError (n : Nat) : ℝ :=
  (Fintype.card (Reg n) : ℝ) * (5 * coefficientError)

private theorem unitaryRoundError_nonneg (n : Nat) : 0 ≤ unitaryRoundError n := by
  unfold unitaryRoundError
  positivity [coefficientError_nonneg]

private theorem rounded_step {n : Nat} (gate : GateAction n) (ok : gate.approxSupported = true)
    (input : Reg n → Gaussian) (hInput : ‖toEuclidean_fromVec (gaussianComplex ∘ input)‖ ≤ 2) :
    ‖toEuclidean_fromVec (gate.apply GateCoefficients.exact (gaussianComplex ∘ input) -
        gaussianComplex ∘ (fun row => roundGaussian (gate.apply GateCoefficients.rational input row)))‖ ≤
      unitaryRoundError n := by
  let _ : Nonempty (Reg n) := ⟨fun _ => false⟩
  apply euclidean_le_of_coordinates _ (by positivity [coefficientError_nonneg])
  intro row
  have hg := (gate.apply_approx ok (gaussianComplex ∘ input) input zero_le_two (le_refl 0)
    (fun i => (amplitude_le _ i).trans hInput) (fun i => by simp) row).2
  have hr := (roundGaussian_error (gate.apply GateCoefficients.rational input row)).trans
    (show 2 / (phaseDenominator : ℝ) ≤ coefficientError by
      norm_num [phaseDenominator, coefficientError])
  change ‖gate.apply GateCoefficients.exact (gaussianComplex ∘ input) row -
    gaussianComplex (roundGaussian (gate.apply GateCoefficients.rational input row))‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

/-- Unitary steps transport existing error isometrically, so fresh rounding errors add. -/
theorem GateAction.run_approx_unitary {n : Nat} (gates : List (GateAction n))
    (supported : gates.all approxSupported = true)
    (unitary : ∀ gate ∈ gates, gate.matrix ∈ unitaryGroup (Reg n) ℂ)
    (ψ : QState (Reg n)) (approx : Reg n → Gaussian) (E : ℝ)
    (hψ : ‖toEuclidean_fromVec ψ‖ ≤ 1)
    (hError : ‖toEuclidean_fromVec (ψ - gaussianComplex ∘ approx)‖ ≤ E)
    (budget : E + gates.length * unitaryRoundError n ≤ 1) :
    ‖toEuclidean_fromVec (run GateCoefficients.exact gates ψ -
        gaussianComplex ∘ runRounded GateCoefficients.rational gates approx)‖ ≤
      E + gates.length * unitaryRoundError n := by
  induction gates generalizing ψ approx E with
  | nil => simpa [run, runRounded] using hError
  | cons gate tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at supported
    have hu := unitary gate (by simp)
    let next := gate.apply GateCoefficients.exact ψ
    let rounded := fun row => roundGaussian (gate.apply GateCoefficients.rational approx row)
    have hn : ‖toEuclidean_fromVec next‖ ≤ 1 := by
      simpa [next, apply_exact, norm_applyGate_of_mem_unitaryGroup hu] using hψ
    have hLe : E ≤ 1 := (le_add_of_nonneg_right
      (show 0 ≤ ((gate :: tail).length : ℝ) * unitaryRoundError n by
        exact mul_nonneg (Nat.cast_nonneg _) (unitaryRoundError_nonneg n))).trans budget
    have hApprox : ‖toEuclidean_fromVec (gaussianComplex ∘ approx)‖ ≤ 2 := by
      rw [show toEuclidean_fromVec (gaussianComplex ∘ approx) =
        toEuclidean_fromVec ψ - toEuclidean_fromVec (ψ - gaussianComplex ∘ approx) by
        ext row; change _ = ψ row - (ψ row - gaussianComplex (approx row)); abel]
      exact (norm_sub_le _ _).trans (by linarith)
    have fresh := rounded_step gate supported.1 approx hApprox
    have old : ‖toEuclidean_fromVec (next - gate.apply GateCoefficients.exact
        (gaussianComplex ∘ approx))‖ ≤ E := by
      rw [show next - gate.apply GateCoefficients.exact (gaussianComplex ∘ approx) =
          ApplyGate gate.matrix (ψ - gaussianComplex ∘ approx) by
        simp only [next, apply_exact, ApplyGate, Matrix.mulVec_sub]]
      rw [norm_applyGate_of_mem_unitaryGroup hu]
      exact hError
    have hnext : ‖toEuclidean_fromVec (next - gaussianComplex ∘ rounded)‖ ≤
        E + unitaryRoundError n := by
      rw [show toEuclidean_fromVec (next - gaussianComplex ∘ rounded) =
          toEuclidean_fromVec (next - gate.apply GateCoefficients.exact (gaussianComplex ∘ approx)) +
          toEuclidean_fromVec (gate.apply GateCoefficients.exact (gaussianComplex ∘ approx) -
            gaussianComplex ∘ rounded) by
          ext row
          simp only [PiLp.add_apply, toEuclidean_fromVec_apply, Pi.sub_apply]
          abel]
      exact (norm_add_le _ _).trans (add_le_add old fresh)
    have hBudget : E + unitaryRoundError n + tail.length * unitaryRoundError n ≤ 1 := by
      simpa [Nat.cast_succ, add_mul, add_left_comm, add_comm, add_assoc] using budget
    have h := ih supported.2 (fun step hm => unitary step (List.mem_cons_of_mem _ hm))
      next rounded (E + unitaryRoundError n) hn hnext hBudget
    rw [run, runRounded_cons]
    simpa [next, rounded, Nat.cast_succ, add_mul, add_left_comm, add_comm, add_assoc] using h

/-- Checked gate-only RIR gives the unitary premises for the lowered evaluator. -/
theorem GateAction.lower_unitary {n : Nat} {steps : List ResolvedInstruction}
    {actions : List (GateAction n)} (ok : steps.all (ResolvedInstruction.isUnitaryGate n) = true)
    (lowered : steps.mapM (lower n false) = .ok actions) :
    ∀ action ∈ actions, action.matrix ∈ unitaryGroup (Reg n) ℂ := by
  induction steps generalizing actions with
  | nil => cases lowered; simp
  | cons step tail ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at lowered
    simp only [List.all_cons, Bool.and_eq_true] at ok
    split at lowered
    · contradiction
    · rename_i action ha
      split at lowered
      · contradiction
      · rename_i rest hr
        cases lowered
        intro elem hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact step.gateMatrix_unitary (fun _ => none) ok.1 (lower_matrix (fun _ => none) ha)
        · exact ih ok.2 hr elem hm

/-- Encode a computational basis state without evaluating any real arithmetic. -/
@[expose] def rationalKet {n : Nat} (source row : Reg n) : Gaussian :=
  if (List.finRange n).all (fun i => row i == source i) then 1 else 0

theorem rationalKet_value {n : Nat} (source row : Reg n) :
    gaussianComplex (rationalKet source row) = Ket source row := by
  have he : ((List.finRange n).all (fun i => row i == source i)) = true ↔ row = source := by
    simp [List.all_eq_true, funext_iff]
  simp only [rationalKet, Ket, he]
  split <;> simp

/-- Convert a uniform entry bound on a two-by-two matrix to an operator norm bound. -/
theorem norm_bool_matrix_le (A : Matrix Bool Bool ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ row col, ‖A row col‖ ≤ b) : ‖A‖ ≤ 4 * b := by
  apply l2_opNorm_le_of_mulVec_le (by positivity)
  intro v
  let s := ‖toEuclidean_fromVec v‖
  have hm (row : Bool) : ‖(A *ᵥ v) row‖ ≤ 2 * b * s := by
    simp only [mulVec, dotProduct, Fintype.sum_bool]
    refine (norm_add_le ..).trans ?_
    simp only [norm_mul]
    have hp (j : Bool) := mul_le_mul (hA row j) (amplitude_le v j) (norm_nonneg _) hb
    nlinarith [hp true, hp false]
  change ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ 4 * b * s
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toEuclidean_fromVec_sq, Fintype.sum_bool]
  have ha (row : Bool) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * b * s)).mpr (hm row)
  nlinarith [ha false, ha true, sq_nonneg (b * s)]

end OracqVerify.RIR
