module

public import OracqVerify.RIR.BlockEncoding
public import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
public import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticNoncommutingLCHS
public import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU

/-! Transfer Qatlib's Taylor and static LCHS estimates to physical success blocks. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.LCHS

open Matrix Polynomial
open Qatlib.Concepts.Execution.WorkspaceCP Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.CoherentSim.FactorialTaylor Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LchsSimulation.StaticLchs
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- Add the ideal Taylor remainder to the certified implementation error of a polynomial block. -/
theorem taylorBranch {J : Type} [Fintype J] (coeff : J → ℝ) (terms : J → Matrix I I ℂ)
    (t : ℝ) (degree : Nat) (u : Matrix S S ℂ) (frame : Matrix S I ℂ) (α δ : ℝ)
    (hTerms : ∀ j, terms j ∈ unitaryGroup I ℂ)
    (hStrength : (∑ j, |coeff j|) * |t| ≤ 1 / 2)
    (encoded : BlockEncoding
      (aeval (∑ j, (coeff j : ℂ) • terms j) (exponentialTaylorPolynomial t (degree + 1)))
      u frame frame α δ) :
    BlockEncoding (hamiltonianEvolution (∑ j, (coeff j : ℂ) • terms j) t)
      u frame frame α (δ + 2 / ((degree + 1).factorial : ℝ)) := by
  apply encoded.perturb (by positivity)
  rw [norm_sub_rev]
  exact factorialTaylor_matrix_remainder_of_unitary coeff terms t degree hTerms hStrength

/-- The explicit operator-norm allowance in Qatlib's static left-endpoint rule. -/
noncomputable def quadratureError (L : Matrix I I ℂ) (t : ℝ) (K N : Nat) : ℝ :=
  2 / (Real.pi * K) + (2 * (K : ℝ) / N) * (2 / Real.pi + t * ‖L‖)

/-- Combine certified branches using Qatlib's scaled LCU, then apply the left-endpoint quadrature
bound. Each physical branch may have its own normalization and error. -/
theorem staticLCU (L H : Matrix I I ℂ) (t : ℝ) (K N : Nat)
    (j₀ : Fin N) (branches : Fin N → Matrix S S ℂ) (frame : Matrix S I ℂ)
    (α ε : Fin N → ℝ)
    (hL : L.PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t) (hK : 0 < K)
    (hBranches : ∀ j, BlockEncoding (hamiltonianEvolution (H + staticLchsGrid K N j • L) t)
      (branches j) frame frame (α j) (ε j)) :
    let c := staticLchsCoeff K N
    let a := ∑ j, ‖c j‖ * α j
    let e := ∑ j, ‖c j‖ * ε j
    BlockEncoding (staticNonunitaryEvolution L H t)
      (coefficientLCUUnitary (scaledLCUCoefficients c α) branches j₀)
      (tagFrame j₀ frame) (tagFrame j₀ frame) a (e + quadratureError L t K N) := by
  dsimp only
  have hN : 0 < N := j₀.pos
  have hα : ∀ j, 0 < α j := fun j => (hBranches j).normalization_pos
  have hc := static_lchs_coefficient_mass_pos K N hK hN
  have hmass : 0 < coefficientMass (scaledLCUCoefficients (staticLchsCoeff K N) α) := by
    obtain ⟨j, hj⟩ := (coefficientMass_pos_iff _).mp hc
    apply (coefficientMass_pos_iff _).mpr
    exact ⟨j, mul_ne_zero hj (Complex.ofReal_ne_zero.mpr (hα j).ne')⟩
  have encoded := scaled_approximate_lcu_encoding j₀
    (fun j => hamiltonianEvolution (H + staticLchsGrid K N j • L) t)
    branches frame frame (staticLchsCoeff K N) α ε hBranches hmass
  have hq := static_noncommuting_lchs_quadrature_error I L H t K N hL hH ht hK hN
  apply encoded.perturb
  · exact (norm_nonneg _).trans hq
  · rw [norm_sub_rev]
    exact hq

/-- Transport a reference encoding through a bound on the discrepancy in the scaled, physical
success block. The remaining part of either unitary extension may differ. -/
theorem physicalBlock {R : Type} [Fintype R] [DecidableEq R] (target : Matrix I I ℂ)
    (reference : Matrix S S ℂ) (rFrame : Matrix S I ℂ)
    (physical : Matrix R R ℂ) (pFrame : Matrix R I ℂ) (α ε δ : ℝ)
    (hReference : BlockEncoding target reference rFrame rFrame α ε)
    (hPhysical : physical ∈ unitaryGroup R ℂ) (hFrame : IsIsometry pFrame)
    (hδ : ‖α • (compress rFrame reference rFrame - compress pFrame physical pFrame)‖ ≤ δ) :
    BlockEncoding target physical pFrame pFrame α (ε + δ) := by
  refine ⟨hPhysical, hFrame, hFrame, hReference.normalization_pos,
    add_nonneg hReference.error_nonneg ((norm_nonneg _).trans hδ), ?_⟩
  calc
    _ = ‖(target - α • compress rFrame reference rFrame) +
        α • (compress rFrame reference rFrame - compress pFrame physical pFrame)‖ := by
      congr 1
      rw [smul_sub]
      abel
    _ ≤ _ := (norm_add_le ..).trans (add_le_add hReference.error_le hδ)

end OracqVerify.Verification.LCHS
