module

public import OracqVerify.Verification.GateEvidence
public import OracqVerify.RIR.ScopedSourceLink

/-! Output-probability contracts for independently bound amplification circuits. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.Amplification

open RIR Matrix Qatlib.Foundations.PureStateMath

def amplitude {source : Program} (evidence : GateEvidence.Certificate source) (target : Bool) :
    Gaussian :=
  evidence.column (GateEvidence.zeroSignal _ false) (GateEvidence.zeroSignal _ target)

noncomputable def exactAmplitude {source : Program} (evidence : GateEvidence.Certificate source)
    (target : Bool) : ℂ :=
  evidence.matrix (GateEvidence.zeroSignal _ target) (GateEvidence.zeroSignal _ false)

/-- Read the signal-zero outcome on the all-zero input, summing over the target bit. -/
noncomputable def successProbability {source : Program} (evidence : GateEvidence.Certificate source) :
    ℝ :=
  ‖exactAmplitude evidence false‖ ^ 2 + ‖exactAmplitude evidence true‖ ^ 2

def checkTwoRegisters (source : Program) : Except String Unit := do
  let entry ← lookupModule source source.entry
  unless entry.registers == [⟨"target", ⟨.bits, 1⟩⟩, ⟨"signal", ⟨.bits, 1⟩⟩] do
    throw "Expected one target wire followed by one signal wire"

structure Replacement (caller bound input : Program) where
  link : ScopedSourceLink caller bound []
  before : GateEvidence.Certificate input
  after : GateEvidence.Certificate bound
  inputWidth : before.trace.wireCount = 2
  outputWidth : after.trace.wireCount = 2
  inputReachable : link.closed.modules.any (fun m => m.name == input.entry) = true
  sameInput : ({bound with entry := input.entry}).resolve = .ok before.trace
  initialZero : GateEvidence.normSquare (amplitude before false) ≤ (549 / 1000 : ℚ) ^ 2
  initialOne : GateEvidence.normSquare (amplitude before true) ≤ (9 / 1000 : ℚ) ^ 2
  amplified : (987 / 1000 : ℚ) ^ 2 ≤ GateEvidence.normSquare (amplitude after false)

def checkReplacement (caller bound input : Program) : Except String (Replacement caller bound input) := do
  checkTwoRegisters caller
  checkTwoRegisters bound
  checkTwoRegisters input
  let link ← verifyScopedSourceLink caller bound
  let before ← GateEvidence.certify input
  let after ← GateEvidence.certify bound
  if inputWidth : before.trace.wireCount = 2 then
    if outputWidth : after.trace.wireCount = 2 then
      if inputReachable : link.closed.modules.any (fun m => m.name == input.entry) then
        if sameInput : ({bound with entry := input.entry}).resolve = .ok before.trace then
          if initialZero : GateEvidence.normSquare (amplitude before false) ≤ (549 / 1000 : ℚ) ^ 2 then
            if initialOne : GateEvidence.normSquare (amplitude before true) ≤ (9 / 1000 : ℚ) ^ 2 then
              if amplified : (987 / 1000 : ℚ) ^ 2 ≤ GateEvidence.normSquare (amplitude after false) then
                return ⟨link, before, after, inputWidth, outputWidth, inputReachable,
                  sameInput, initialZero, initialOne, amplified⟩
              else throw "Amplified success probability falls below the budget"
            else throw "Initial success probability exceeds the budget"
          else throw "Initial success probability exceeds the budget"
        else throw "Bound amplifier changes the input preparation"
      else throw "The shared preparation is unreachable in the bound amplifier"
    else throw "Unexpected bound amplifier width"
  else throw "Unexpected input preparation width"

private theorem amplitudeError {source : Program} (evidence : GateEvidence.Certificate source)
    (target : Bool) :
    ‖exactAmplitude evidence target - gaussianComplex (amplitude evidence target)‖ ≤
      (1 : ℝ) / 10^20 :=
  evidence.entry_error _ _

private theorem amplitudeUpper {source : Program} (evidence : GateEvidence.Certificate source)
    (target : Bool) {bound : ℚ} (nonneg : 0 ≤ bound)
    (checked : GateEvidence.normSquare (amplitude evidence target) ≤ bound ^ 2) :
    ‖exactAmplitude evidence target‖ ≤ (bound : ℝ) + 1 / 10^20 := by
  have hb : (0 : ℝ) ≤ (bound : ℝ) := by exact_mod_cast nonneg
  have h := (sq_le_sq₀ (norm_nonneg _) hb).mp (by
    rw [GateEvidence.norm_square]
    exact_mod_cast checked)
  have err := (norm_sub_norm_le (exactAmplitude evidence target)
    (gaussianComplex (amplitude evidence target))).trans (amplitudeError evidence target)
  linarith

theorem Replacement.sound {caller bound input : Program} (cert : Replacement caller bound input) :
    input.matrix (fun _ => none) = .ok ⟨cert.before.trace.wireCount, cert.before.matrix⟩ ∧
      bound.matrix (fun _ => none) = .ok ⟨cert.after.trace.wireCount, cert.after.matrix⟩ ∧
      successProbability cert.before ≤ (31 : ℝ) / 100 ∧
      (97 : ℝ) / 100 ≤ successProbability cert.after := by
  refine ⟨cert.before.sound.1, cert.after.sound.1, ?_, ?_⟩
  · have zero := amplitudeUpper cert.before false (by norm_num) cert.initialZero
    have one := amplitudeUpper cert.before true (by norm_num) cert.initialOne
    have hzero : ‖exactAmplitude cert.before false‖ ≤ 11 / 20 := zero.trans (by norm_num)
    have hone : ‖exactAmplitude cert.before true‖ ≤ 1 / 100 := one.trans (by norm_num)
    unfold successProbability
    exact (add_le_add ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hzero)
      ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hone)).trans (by norm_num)
  · have approx : (987 : ℝ) / 1000 ≤ ‖gaussianComplex (amplitude cert.after false)‖ := by
      apply (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp
      rw [GateEvidence.norm_square]
      have numeric := (Rat.cast_le (K := ℝ)).mpr cert.amplified
      norm_num at numeric ⊢
      exact numeric
    have err := (norm_sub_norm_le (gaussianComplex (amplitude cert.after false))
      (exactAmplitude cert.after false)).trans ((norm_sub_rev ..).le.trans (amplitudeError cert.after false))
    have lower : (197 : ℝ) / 200 ≤ ‖exactAmplitude cert.after false‖ := by linarith
    unfold successProbability
    calc
      _ ≤ ((197 : ℝ) / 200)^2 := by norm_num
      _ ≤ ‖exactAmplitude cert.after false‖ ^ 2 :=
        (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mpr lower
      _ ≤ _ := le_add_of_nonneg_right (sq_nonneg _)

end OracqVerify.Verification.Amplification
