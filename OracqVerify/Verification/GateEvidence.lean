module

public import OracqVerify.RIR.RationalUnitary

/-! Executable, checked entry approximations for small serialized gate-only circuits. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.GateEvidence

open RIR Matrix Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open scoped Matrix

structure Certificate (source : Program) where
  trace : ResolvedProgram
  resolved : source.resolve = .ok trace
  gates : trace.instructions.all (ResolvedInstruction.isUnitaryGate trace.wireCount) = true
  actions : List (GateAction trace.wireCount)
  lowered : trace.instructions.mapM (GateAction.lower trace.wireCount false) = .ok actions
  supported : actions.all GateAction.approxSupported = true
  width : trace.wireCount ≤ 10
  size : actions.length ≤ 512

def certify (source : Program) : Except String (Certificate source) := do
  match resolved : source.resolve with
  | .error reason => throw reason
  | .ok trace =>
    if width : trace.wireCount ≤ 10 then
      if gates : trace.instructions.all (ResolvedInstruction.isUnitaryGate trace.wireCount) then
        match lowered : trace.instructions.mapM (GateAction.lower trace.wireCount false) with
        | .error reason => throw reason
        | .ok actions =>
          if size : actions.length ≤ 512 then
            if supported : actions.all GateAction.approxSupported then
              return ⟨trace, resolved, gates, actions, lowered, supported, width, size⟩
            else throw "Gate angles exceed the checked rational domain"
          else throw "Gate evidence supports at most 512 resolved instructions"
      else throw "Expected a unitary gate word"
    else throw "Gate evidence supports at most ten wires"

/-- Reuse gate evidence for a separately decoded program with the same resolved word. -/
def Certificate.ofResolution {first second : Program} (cert : Certificate first)
    (resolved : second.resolve = .ok cert.trace) : Certificate second :=
  ⟨cert.trace, resolved, cert.gates, cert.actions, cert.lowered,
    cert.supported, cert.width, cert.size⟩

noncomputable def Certificate.matrix {source : Program} (cert : Certificate source) :
    WireMatrix cert.trace.wireCount :=
  wordMatrix (cert.actions.map GateAction.matrix)

def Certificate.column {source : Program} (cert : Certificate source) (input : Reg cert.trace.wireCount) :
    Reg cert.trace.wireCount → Gaussian :=
  GateAction.runRational cert.actions (rationalKet input)

theorem Certificate.sound {source : Program} (cert : Certificate source) :
    source.matrix (fun _ => none) = .ok ⟨cert.trace.wireCount, cert.matrix⟩ ∧
      cert.matrix ∈ unitaryGroup (Reg cert.trace.wireCount) ℂ := by
  have evaluated := GateAction.resolved_matrix (fun _ => none) cert.lowered
  constructor
  · simp [Program.matrix, cert.resolved, evaluated, Certificate.matrix, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  · have actions := GateAction.lower_unitary cert.gates cert.lowered
    apply wordMatrix_unitary
    simpa only [List.mem_map] using fun gate ⟨a, ha, h⟩ => h ▸ actions a ha

private theorem errorBudget {n steps : Nat} (width : n ≤ 10) (size : steps ≤ 512) :
    (steps : ℝ) * unitaryRoundError n ≤ 1 / 10^20 := by
  have cardLe : Fintype.card (Reg n) ≤ 1024 := by
    rw [show Fintype.card (Reg n) = 2 ^ n by simp [Reg]]
    exact Nat.pow_le_pow_right (by decide) width
  have hCard : (Fintype.card (Reg n) : ℝ) ≤ 1024 := by exact_mod_cast cardLe
  have hSize : (steps : ℝ) ≤ 512 := by exact_mod_cast size
  unfold unitaryRoundError
  calc
    _ ≤ (512 : ℝ) * (1024 * (5 * coefficientError)) := by
      gcongr <;> positivity [coefficientError_nonneg]
    _ ≤ _ := by norm_num [coefficientError]

theorem Certificate.entry_error {source : Program} (cert : Certificate source)
    (row col : Reg cert.trace.wireCount) :
    ‖cert.matrix row col - gaussianComplex (cert.column col row)‖ ≤ (1 : ℝ) / 10^20 := by
  let input := Ket col
  have hr : gaussianComplex ∘ rationalKet col = input := funext (rationalKet_value _)
  have hNorm : ‖toEuclidean_fromVec input‖ ≤ 1 :=
    ((normalized_iff_norm_toEuclidean_fromVec input).mp (normalized_ket _)).le
  have error := errorBudget cert.width cert.size
  have budget : (0 : ℝ) + cert.actions.length * unitaryRoundError cert.trace.wireCount ≤ 1 := by
    exact (zero_add _).le.trans (error.trans (by norm_num))
  have initial : ‖toEuclidean_fromVec (input - gaussianComplex ∘ rationalKet col)‖ ≤ 0 := by
    rw [hr, sub_self]
    have zero : toEuclidean_fromVec (0 : QState (Reg cert.trace.wireCount)) = 0 := by
      ext i
      simp
    rw [zero, norm_zero]
  have approx := GateAction.run_approx_unitary cert.actions cert.supported
    (GateAction.lower_unitary cert.gates cert.lowered) input (rationalKet col) 0 hNorm initial budget
  rw [GateAction.run_exact, zero_add] at approx
  have coordinate := (PiLp.norm_apply_le (toEuclidean_fromVec _) row).trans approx
  simpa [input, Certificate.matrix, Certificate.column, GateAction.runRational_eq,
    applyGate_eq_mulVec_ket] using coordinate.trans error

/-- Read two entries after propagating one rounded column, sharing its intermediate states. -/
def runPair {n : Nat} (coeff : GateCoefficients Gaussian) (row₀ row₁ : Reg n) :
    List (GateAction n) → (Reg n → Gaussian) → Gaussian × Gaussian
  | [], state => (state row₀, state row₁)
  | step :: rest, state =>
    let basis := bitVecEquiv n
    let table := Vector.ofFn fun index => roundGaussian (step.apply coeff state (basis.symm index))
    runPair coeff row₀ row₁ rest (fun row => table[(basis row).val])

theorem runPair_eq {n : Nat} (coeff : GateCoefficients Gaussian) (row₀ row₁ : Reg n)
    (actions : List (GateAction n)) (state : Reg n → Gaussian) :
    runPair coeff row₀ row₁ actions state =
      (GateAction.runRounded coeff actions state row₀, GateAction.runRounded coeff actions state row₁) := by
  induction actions generalizing state with
  | nil => rfl
  | cons step rest ih =>
    rw [runPair, ih, GateAction.runRounded_cons]
    simp

def Certificate.columnPair {source : Program} (cert : Certificate source)
    (input row₀ row₁ : Reg cert.trace.wireCount) : Gaussian × Gaussian :=
  let samples := (cert.actions.flatMap GateAction.phaseSamples).eraseDups
  let phases := samples.map fun value => (value, rationalPhase value)
  runPair (GateCoefficients.rationalWith (phaseLookup phases)) row₀ row₁ cert.actions (rationalKet input)

theorem Certificate.columnPair_eq {source : Program} (cert : Certificate source)
    (input row₀ row₁ : Reg cert.trace.wireCount) :
    cert.columnPair input row₀ row₁ = (cert.column input row₀, cert.column input row₁) := by
  rw [Certificate.columnPair, runPair_eq]
  rfl

def l1 (z : Gaussian) : ℚ := |z.re| + |z.im|

theorem norm_le_l1 (z : Gaussian) : ‖gaussianComplex z‖ ≤ (l1 z : ℝ) := by
  simpa [l1, Rat.cast_abs] using Complex.norm_le_abs_re_add_abs_im (gaussianComplex z)

def normSquare (z : Gaussian) : ℚ := z.re ^ 2 + z.im ^ 2

theorem norm_square (z : Gaussian) : ‖gaussianComplex z‖ ^ 2 = (normSquare z : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [normSquare, pow_two]

def zeroSignal (n : Nat) (target : Bool) : Reg n := fun i => if i.val = 0 then target else false

end OracqVerify.Verification.GateEvidence
