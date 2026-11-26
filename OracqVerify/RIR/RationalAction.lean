module

public import OracqVerify.RIR.RationalPhase
public import OracqVerify.RIR.BlockEncoding

/-! Executable rational simulation with a proof of its discrepancy from the RIR amplitudes. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

def signedAngle (a : Lean.JsonNumber) (inverse : Bool) : ℚ :=
  if inverse then -rationalAngle a else rationalAngle a

theorem abs_signedAngle (a : Lean.JsonNumber) (inverse : Bool) :
    |signedAngle a inverse| = |rationalAngle a| := by cases inverse <;> simp [signedAngle]

/-- A rational lower endpoint for the magnitude of a Hadamard entry. -/
def rationalHadamard : ℚ :=
  70710678118654752440084436210484903928483593768847 / (10 : ℚ) ^ (50 : Nat)

private theorem hadamardCoefficient_error :
    |(Real.sqrt 2)⁻¹ - (rationalHadamard : ℝ)| ≤ coefficientError := by
  let h := (Real.sqrt (2 : ℝ))⁻¹
  let l : ℝ := rationalHadamard
  let u := l + (1 : ℝ) / (10 : ℝ) ^ (50 : Nat)
  have hSq : h ^ 2 = 1 / 2 := by
    rw [show h = (Real.sqrt 2)⁻¹ from rfl, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hNonneg : 0 ≤ h := by positivity
  have lNonneg : 0 ≤ l := by norm_num [l, rationalHadamard]
  have uNonneg : 0 ≤ u := by positivity
  have lower : l ≤ h := by
    apply (sq_le_sq₀ lNonneg hNonneg).mp
    rw [hSq]
    norm_num [l, rationalHadamard]
  have upper : h ≤ u := by
    apply (sq_le_sq₀ hNonneg uNonneg).mp
    rw [hSq]
    norm_num [u, l, rationalHadamard]
  change |h - l| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr lower)]
  calc
    h - l ≤ u - l := sub_le_sub_right upper l
    _ = (1 : ℝ) / 10 ^ (50 : Nat) := by dsimp [u]; ring
    _ ≤ coefficientError := by norm_num [coefficientError]

def GateCoefficients.rationalWith (phaseValue : ℚ → Gaussian) : GateCoefficients Gaussian where
  zero := 0
  add := (· + ·)
  mul := (· * ·)
  phase a inv := phaseValue (signedAngle a inv)
  unary
    | .h, _, row, col => ⟨if row && col then -rationalHadamard else rationalHadamard, 0⟩
    | .x, _, row, col => if row == col then 0 else 1
    | .z, _, row, col => if row == col then (if row then -1 else 1) else 0
    | .ry a, inv, row, col =>
      let z := phaseValue (signedAngle a inv / 2)
      ⟨if row == col then z.re else if row then z.im else -z.im, 0⟩

def GateCoefficients.rational : GateCoefficients Gaussian := rationalWith rationalPhase

/-- The phase-series domain and fixed-coefficient gates supported by the numerical checker. -/
def GateAction.approxSupported {n : Nat} : GateAction n → Bool
  | .unary (.ry a) _ _ => decide (|rationalAngle a / 2| ≤ 4)
  | .unary _ _ _ => true
  | .phase a _ => decide (|rationalAngle a| ≤ 4)
  | .control _ _ body => body.approxSupported

theorem exactPhase_signed (a : Lean.JsonNumber) (inv : Bool) :
    GateCoefficients.exact.phase a inv =
      Complex.exp (((signedAngle a inv : ℝ) : ℂ) * Complex.I) := by
  cases inv <;>
    simp [GateCoefficients.exact, signedAngle, ← Complex.exp_conj, map_mul]

private theorem exactRotation_signed (a : Lean.JsonNumber) (inv : Bool) (row col : Bool) :
    GateCoefficients.exact.unary (.ry a) inv row col =
      rotationY (signedAngle a inv : ℝ) row col := by
  cases inv with
  | false => simp [GateCoefficients.exact, signedAngle, unaryMatrix]
  | true =>
    change (rotationY (angleValue a))ᴴ row col = rotationY (signedAngle a true : ℝ) row col
    rw [rotationY_adjoint]
    simp [signedAngle]

private theorem rationalPhase_re_error (x : ℚ) (h : |x| ≤ 4) :
    |Real.cos (x : ℝ) - (rationalPhase x).re| ≤ coefficientError := by
  have he := Complex.abs_re_le_norm
    (Complex.exp (((x : ℝ) : ℂ) * Complex.I) - gaussianComplex (rationalPhase x))
  simpa only [Complex.sub_re, Complex.exp_ofReal_mul_I_re, gaussianComplex_re] using
    he.trans (rationalPhase_error x h)

private theorem rationalPhase_im_error (x : ℚ) (h : |x| ≤ 4) :
    |Real.sin (x : ℝ) - (rationalPhase x).im| ≤ coefficientError := by
  have he := Complex.abs_im_le_norm
    (Complex.exp (((x : ℝ) : ℂ) * Complex.I) - gaussianComplex (rationalPhase x))
  simpa only [Complex.sub_im, Complex.exp_ofReal_mul_I_im, gaussianComplex_im] using
    he.trans (rationalPhase_error x h)

private theorem unary_approx {n : Nat} (gate : UnaryGate) (wire : Fin n) (inv row col : Bool)
    (ok : (GateAction.unary gate wire inv).approxSupported = true) :
    ‖GateCoefficients.exact.unary gate inv row col -
      gaussianComplex (GateCoefficients.rational.unary gate inv row col)‖ ≤ coefficientError := by
  cases gate with
  | h =>
    let h := (Real.sqrt (2 : ℝ))⁻¹
    let l : ℝ := rationalHadamard
    have positive : ‖h - l‖ ≤ coefficientError := by
      simpa [h, l, Real.norm_eq_abs] using hadamardCoefficient_error
    have negative : ‖-h + l‖ ≤ coefficientError := by
      rw [show -h + l = -(h - l) by ring, norm_neg]
      exact positive
    have positiveComplex : ‖(h : ℂ) - (l : ℂ)‖ ≤ coefficientError := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      exact positive
    have negativeComplex : ‖((-h : ℝ) : ℂ) + (l : ℂ)‖ ≤ coefficientError := by
      rw [← Complex.ofReal_add, Complex.norm_real]
      exact negative
    cases inv <;> cases row <;> cases col <;>
      simp [GateCoefficients.exact, GateCoefficients.rational, GateCoefficients.rationalWith,
        unaryMatrix, Hadamard, ← Complex.ofReal_inv, ← Complex.ofReal_neg] <;>
        first | exact positiveComplex | exact negativeComplex
  | x =>
    cases inv <;> cases row <;> cases col <;>
      simpa [GateCoefficients.exact, GateCoefficients.rational, GateCoefficients.rationalWith,
        unaryMatrix, PauliX, permMatrix]
        using coefficientError_nonneg
  | z =>
    cases inv <;> cases row <;> cases col <;>
      simpa [GateCoefficients.exact, GateCoefficients.rational, GateCoefficients.rationalWith,
        unaryMatrix, PauliZ,
        Matrix.diagonal_apply] using coefficientError_nonneg
  | ry a =>
    have ha : |rationalAngle a / 2| ≤ 4 := of_decide_eq_true ok
    let x := signedAngle a inv / 2
    have hx : |x| ≤ 4 := by
      simpa [x, abs_div, abs_signedAngle] using ha
    have hc := rationalPhase_re_error x hx
    have hs := rationalPhase_im_error x hx
    rw [exactRotation_signed]
    have he : ((signedAngle a inv : ℝ) / 2) = (x : ℝ) := by simp [x]
    have hc' : ‖(Real.cos (x : ℝ) : ℂ) - gaussianComplex ⟨(rationalPhase x).re, 0⟩‖ ≤
        coefficientError := by
      simpa only [gaussianComplex_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hc
    have hs' : ‖(Real.sin (x : ℝ) : ℂ) - gaussianComplex ⟨(rationalPhase x).im, 0⟩‖ ≤
        coefficientError := by
      simpa only [gaussianComplex_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hs
    have hn : ‖-(Real.sin (x : ℝ) : ℂ) - gaussianComplex ⟨-(rationalPhase x).im, 0⟩‖ ≤
        coefficientError := by
      simpa only [gaussianComplex_real, Rat.cast_neg, neg_sub_neg, norm_sub_rev] using hs'
    cases row <;> cases col
    · change ‖rotationY (signedAngle a inv : ℝ) false false - gaussianComplex
        ⟨(rationalPhase x).re, 0⟩‖ ≤ _
      simpa only [rotationY, eq_self, ite_true, he] using hc'
    · change ‖rotationY (signedAngle a inv : ℝ) false true - gaussianComplex
        ⟨-(rationalPhase x).im, 0⟩‖ ≤ _
      simpa only [rotationY, Bool.false_eq_true, ite_false, he] using hn
    · change ‖rotationY (signedAngle a inv : ℝ) true false - gaussianComplex
        ⟨(rationalPhase x).im, 0⟩‖ ≤ _
      simpa only [rotationY, Bool.true_eq_false, ite_false, ite_true, he] using hs'
    · change ‖rotationY (signedAngle a inv : ℝ) true true - gaussianComplex
        ⟨(rationalPhase x).re, 0⟩‖ ≤ _
      simpa only [rotationY, eq_self, ite_true, he] using hc'

private theorem unary_norm (gate : UnaryGate) (inv row col : Bool) :
    ‖GateCoefficients.exact.unary gate inv row col‖ ≤ 1 := by
  cases inv with
  | false => exact entry_norm_bound_of_unitary (unaryMatrix_unitary gate) row col
  | true =>
    have h := (Unitary.star_mem_iff).mpr (unaryMatrix_unitary gate)
    exact entry_norm_bound_of_unitary h row col

private theorem phase_approx {n : Nat} (a : Lean.JsonNumber) (inv : Bool)
    (ok : (GateAction.phase a inv : GateAction n).approxSupported = true) :
    ‖GateCoefficients.exact.phase a inv -
      gaussianComplex (GateCoefficients.rational.phase a inv)‖ ≤ coefficientError := by
  rw [exactPhase_signed]
  exact rationalPhase_error _ ((abs_signedAngle a inv).le.trans (of_decide_eq_true ok))

private theorem phase_norm (a : Lean.JsonNumber) (inv : Bool) :
    ‖GateCoefficients.exact.phase a inv‖ ≤ 1 := by
  rw [exactPhase_signed, Complex.norm_exp_mul_I]
  simp

private theorem product_error (a b x y : ℂ) {B E : ℝ}
    (ha : ‖a‖ ≤ 1) (hab : ‖a - b‖ ≤ coefficientError) (hx : ‖x‖ ≤ B)
    (hxy : ‖x - y‖ ≤ E) :
    ‖a * x‖ ≤ B ∧ ‖a * x - b * y‖ ≤ coefficientError * B + 2 * E := by
  have hb : ‖b‖ ≤ 2 := by
    calc
      ‖b‖ ≤ ‖b - a‖ + ‖a‖ := norm_le_norm_sub_add _ _
      _ ≤ 2 := by rw [norm_sub_rev b a]; linarith [coefficientError_le_one]
  refine ⟨?_, ?_⟩
  · rw [norm_mul]
    nlinarith [mul_le_mul ha hx (norm_nonneg x) zero_le_one]
  · rw [show a * x - b * y = (a - b) * x + b * (x - y) by ring]
    refine (norm_add_le ..).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul hab hx (norm_nonneg _) coefficientError_nonneg)
      (mul_le_mul hb hxy (norm_nonneg _) zero_le_two)

theorem GateAction.apply_approx {n : Nat} (gate : GateAction n)
    (ok : gate.approxSupported = true) (ψ : Reg n → ℂ) (approx : Reg n → Gaussian)
    {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hx : ∀ row, ‖ψ row‖ ≤ B) (he : ∀ row, ‖ψ row - gaussianComplex (approx row)‖ ≤ E)
    (row : Reg n) :
    ‖gate.apply GateCoefficients.exact ψ row‖ ≤ 2 * B ∧
      ‖gate.apply GateCoefficients.exact ψ row -
        gaussianComplex (gate.apply GateCoefficients.rational approx row)‖ ≤
        4 * E + 2 * coefficientError * B := by
  induction gate generalizing ψ approx with
  | unary g wire inv =>
    have h (bit : Bool) :=
      product_error _ _ _ _ (unary_norm g inv (row wire) bit)
        (unary_approx g wire inv (row wire) bit ok) (hx (updateBit row wire bit))
        (he (updateBit row wire bit))
    simp only [apply, GateCoefficients.exact, GateCoefficients.rational,
      GateCoefficients.rationalWith] at *
    refine ⟨(norm_add_le ..).trans (by linarith [(h false).1, (h true).1]), ?_⟩
    simp only [map_add, map_mul]
    rw [add_sub_add_comm]
    exact (norm_add_le ..).trans (by linarith [(h false).2, (h true).2])
  | phase a inv =>
    obtain ⟨hb, ha⟩ := product_error _ _ _ _ (phase_norm a inv) (phase_approx a inv ok)
      (hx row) (he row)
    simp only [apply, GateCoefficients.exact, GateCoefficients.rational,
      GateCoefficients.rationalWith, map_mul] at *
    exact ⟨hb.trans (by linarith), ha.trans (by nlinarith [mul_nonneg coefficientError_nonneg hB])⟩
  | control view value body ih =>
    simp only [apply]
    split
    · apply ih ok
      · intro col
        by_cases active : guardEnabled view value col = true
        · simpa [active] using hx col
        · simpa [active, GateCoefficients.exact] using hB
      · intro col
        by_cases active : guardEnabled view value col = true
        · simpa [active] using he col
        · simpa [active, GateCoefficients.exact, GateCoefficients.rational,
            GateCoefficients.rationalWith] using hE
    · exact ⟨(hx row).trans (by linarith),
        (he row).trans (by nlinarith [mul_nonneg coefficientError_nonneg hB])⟩

/-- Materialize a finite state vector once before proceeding to the next gate. -/
def cacheState {α : Type} {n : Nat} (state : Reg n → α) : Reg n → α :=
  let e := bitVecEquiv n
  let table := Vector.ofFn (fun i => state (e.symm i))
  fun row => table[(e row).val]

theorem cacheState_eq {α : Type} {n : Nat} (state : Reg n → α) : cacheState state = state := by
  funext row
  simp [cacheState]

/-- Round and materialize the whole state before the recursive call. Capturing the vector
in the argument closure shares its entries across accesses by the next gate. -/
def GateAction.runRounded {n : Nat} (coeff : GateCoefficients Gaussian) :
    List (GateAction n) → (Reg n → Gaussian) → Reg n → Gaussian
  | [], state => state
  | step :: rest, state =>
    let basis := bitVecEquiv n
    let table := Vector.ofFn fun index => roundGaussian (step.apply coeff state (basis.symm index))
    runRounded coeff rest (fun row => table[(basis row).val])

theorem GateAction.runRounded_cons {n : Nat} (coeff : GateCoefficients Gaussian)
    (step : GateAction n) (rest : List (GateAction n)) (state : Reg n → Gaussian) :
    runRounded coeff (step :: rest) state =
      runRounded coeff rest (fun row => roundGaussian (step.apply coeff state row)) := by
  rw [runRounded]
  congr 1
  funext row
  simp

theorem GateAction.run_approx {n : Nat} (gates : List (GateAction n))
    (ok : gates.all approxSupported = true) (ψ : Reg n → ℂ) (approx : Reg n → Gaussian)
    {B E : ℝ} (hB : 1 ≤ B) (hE : 0 ≤ E)
    (hx : ∀ row, ‖ψ row‖ ≤ B) (he : ∀ row, ‖ψ row - gaussianComplex (approx row)‖ ≤ E)
    (row : Reg n) :
    ‖run GateCoefficients.exact gates ψ row -
      gaussianComplex (runRounded GateCoefficients.rational gates approx row)‖ ≤
      4 ^ gates.length * E + 2 * coefficientError * B * (4 ^ gates.length - 2 ^ gates.length) := by
  induction gates generalizing B E ψ approx with
  | nil => simpa [run, runRounded] using he row
  | cons gate tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ok
    have hB' : 0 ≤ B := zero_le_one.trans hB
    have hg r := gate.apply_approx ok.1 ψ approx hB' hE hx he r
    have step_round (r : Reg n) :
        ‖gate.apply GateCoefficients.exact ψ r -
          gaussianComplex (roundGaussian (gate.apply GateCoefficients.rational approx r))‖ ≤
          4 * E + 4 * coefficientError * B := by
      refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        ((add_le_add (hg r).2 (roundGaussian_error _)).trans ?_)
      have hr : 2 / (phaseDenominator : ℝ) ≤ coefficientError := by
        norm_num [phaseDenominator, coefficientError]
      nlinarith [mul_le_mul_of_nonneg_left hB coefficientError_nonneg,
        mul_nonneg coefficientError_nonneg hB']
    have hrun := ih ok.2 _ _ (by linarith : 1 ≤ 2 * B)
      (by positivity [coefficientError_nonneg] : 0 ≤ 4 * E + 4 * coefficientError * B)
      (fun r => (hg r).1) step_round
    rw [run, runRounded_cons]
    refine hrun.trans_eq ?_
    simp only [List.length_cons, pow_succ]
    ring

def GateAction.phaseSamples {n : Nat} : GateAction n → List ℚ
  | .unary (.ry a) _ inv => [signedAngle a inv / 2]
  | .phase a inv => [signedAngle a inv]
  | .control _ _ body => body.phaseSamples
  | _ => []

def phaseLookup (table : List (ℚ × Gaussian)) (angle : ℚ) : Gaussian :=
  match table.lookup angle with
  | some value => value
  | none => rationalPhase angle

theorem phaseLookup_eq (samples : List ℚ) (angle : ℚ) :
    phaseLookup (samples.map (fun a => (a, rationalPhase a))) angle = rationalPhase angle := by
  induction samples with
  | nil => rfl
  | cons head tail ih =>
    by_cases h : angle = head
    · subst head
      simp [phaseLookup]
    · have hb : (angle == head) = false := by simp [h]
      simpa [phaseLookup, List.lookup, hb] using ih

/-- Lookup the rounded phases by exact rational angle and share the finite state at each step. -/
def GateAction.runRational {n : Nat} (steps : List (GateAction n))
    (state : Reg n → Gaussian) : Reg n → Gaussian :=
  let samples := (steps.flatMap phaseSamples).eraseDups
  let table := samples.map fun x => (x, rationalPhase x)
  runRounded (GateCoefficients.rationalWith (phaseLookup table)) steps state

theorem GateAction.runRational_eq {n : Nat} (steps : List (GateAction n))
    (state : Reg n → Gaussian) :
    runRational steps state = runRounded GateCoefficients.rational steps state := by
  unfold runRational
  dsimp only
  have h : phaseLookup ((steps.flatMap phaseSamples).eraseDups.map (fun x => (x, rationalPhase x))) =
      rationalPhase := funext (phaseLookup_eq _)
  rw [h]
  rfl

end OracqVerify.RIR
