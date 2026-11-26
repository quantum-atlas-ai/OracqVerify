module

public import OracqVerify.RIR.GateAction
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-! Rational evaluation of the imaginary exponential, with a certified Taylor and rounding error. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

/-- The executable Gaussian rational scalar type. -/
abbrev Gaussian := QuadraticAlgebra ℚ (-1) 0

/-- Interpret a Gaussian rational exactly as a complex number. -/
def gaussianComplex : Gaussian →+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by apply Complex.ext <;> simp
  map_mul' z w := by
    apply Complex.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

@[simp] theorem gaussianComplex_re (z : Gaussian) : (gaussianComplex z).re = (z.re : ℝ) := rfl
@[simp] theorem gaussianComplex_im (z : Gaussian) : (gaussianComplex z).im = (z.im : ℝ) := rfl

theorem gaussianComplex_real (x : ℚ) :
    gaussianComplex (⟨x, 0⟩ : Gaussian) = (x : ℂ) := by apply Complex.ext <;> simp

theorem gaussianComplex_ofReal (x : ℚ) :
    gaussianComplex (⟨x, 0⟩ : Gaussian) = ((x : ℝ) : ℂ) := by apply Complex.ext <;> simp

theorem gaussianComplex_imaginary (x : ℚ) :
    gaussianComplex (⟨0, x⟩ : Gaussian) = ((x : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The decimal angle used by the resolver, interpreted as a rational number. -/
def rationalAngle (a : Lean.JsonNumber) : ℚ :=
  (a.mantissa : ℚ) / (10 : ℚ) ^ a.exponent

@[simp] theorem rationalAngle_real (a : Lean.JsonNumber) :
    ((rationalAngle a : ℚ) : ℝ) = angleValue a := by simp [rationalAngle, angleValue]

/-- Taylor partial sum of the imaginary exponential in Gaussian rationals. -/
def rationalPhaseSeries (x : ℚ) : Nat → Gaussian
  | 0 => 0
  | n + 1 =>
    rationalPhaseSeries x n + (⟨0, x⟩ : Gaussian) ^ n * ⟨(n.factorial : ℚ)⁻¹, 0⟩

theorem rationalPhaseSeries_complex (x : ℚ) (n : Nat) :
    gaussianComplex (rationalPhaseSeries x n) =
      ∑ k ∈ Finset.range n, (((x : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
  induction n with
  | zero => simp [rationalPhaseSeries]
  | succ n ih =>
    simp [rationalPhaseSeries, ih, Finset.sum_range_succ,
      gaussianComplex_imaginary, div_eq_mul_inv]

/-- A common denominator keeps the executable gate coefficients small across long words. -/
def phaseDenominator : ℚ := (10 : ℚ) ^ (46 : Nat)

def rationalRound (x : ℚ) : ℚ := (⌊x * phaseDenominator⌋ : ℚ) / phaseDenominator

private theorem rationalRound_error (x : ℚ) : |x - rationalRound x| ≤ phaseDenominator⁻¹ := by
  have hd : 0 < phaseDenominator := by norm_num [phaseDenominator]
  have h₁ := Int.floor_le (x * phaseDenominator)
  have h₂ := Int.lt_floor_add_one (x * phaseDenominator)
  have h₃ : rationalRound x ≤ x := by
    exact (div_le_iff₀ hd).2 h₁
  rw [abs_of_nonneg (sub_nonneg.mpr h₃)]
  have h₄ : x - rationalRound x ≤ 1 / phaseDenominator := by
    apply (le_div_iff₀ hd).2
    rw [sub_mul]
    have he : rationalRound x * phaseDenominator = (⌊x * phaseDenominator⌋ : ℚ) := by
      simp [rationalRound, hd.ne']
    rw [he]
    linarith
  simpa using h₄

def roundGaussian (z : Gaussian) : Gaussian :=
  ⟨rationalRound z.re, rationalRound z.im⟩

theorem roundGaussian_error (z : Gaussian) :
    ‖gaussianComplex z - gaussianComplex (roundGaussian z)‖ ≤ 2 / (phaseDenominator : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  change |(z.re : ℝ) - (rationalRound z.re : ℝ)| +
    |(z.im : ℝ) - (rationalRound z.im : ℝ)| ≤ _
  have hre : |(z.re : ℝ) - (rationalRound z.re : ℝ)| ≤ (phaseDenominator : ℝ)⁻¹ := by
    exact_mod_cast rationalRound_error z.re
  have him : |(z.im : ℝ) - (rationalRound z.im : ℝ)| ≤ (phaseDenominator : ℝ)⁻¹ := by
    exact_mod_cast rationalRound_error z.im
  linarith [show (2 : ℝ) / (phaseDenominator : ℝ) =
    2 * (phaseDenominator : ℝ)⁻¹ by rw [div_eq_mul_inv]]

/-- Use a rational partial sum followed by coordinate rounding. -/
def rationalPhase (x : ℚ) : Gaussian :=
  roundGaussian (rationalPhaseSeries x 72)

noncomputable def coefficientError : ℝ := (10 : ℝ)⁻¹ ^ (44 : Nat)

theorem coefficientError_nonneg : 0 ≤ coefficientError := by norm_num [coefficientError]
theorem coefficientError_le_one : coefficientError ≤ 1 := by norm_num [coefficientError]

theorem rationalPhase_error (x : ℚ) (hx : |x| ≤ 4) :
    ‖Complex.exp (((x : ℝ) : ℂ) * Complex.I) - gaussianComplex (rationalPhase x)‖ ≤
      coefficientError := by
  let z := ((x : ℝ) : ℂ) * Complex.I
  have hb : ‖z‖ ≤ 4 := by
    simpa [z, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      (show |(x : ℝ)| ≤ 4 by exact_mod_cast hx)
  have ht := Complex.exp_bound' (x := z) (n := 72)
    (by norm_num; linarith : ‖z‖ / (73 : Nat) ≤ (1 : ℝ) / 2)
  rw [← rationalPhaseSeries_complex x 72] at ht
  have hseries : ‖Complex.exp z - gaussianComplex (rationalPhaseSeries x 72)‖ ≤
      4 ^ (72 : Nat) / ((72 : Nat).factorial : ℝ) * 2 := by
    refine ht.trans ?_
    gcongr
  have hround := roundGaussian_error (rationalPhaseSeries x 72)
  calc
    _ ≤ ‖Complex.exp z - gaussianComplex (rationalPhaseSeries x 72)‖ +
        ‖gaussianComplex (rationalPhaseSeries x 72) - gaussianComplex (rationalPhase x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 ^ (72 : Nat) / ((72 : Nat).factorial : ℝ) * 2 + 2 / (phaseDenominator : ℝ) :=
      add_le_add hseries hround
    _ ≤ _ := by norm_num [coefficientError, phaseDenominator, Nat.factorial]

end OracqVerify.RIR
