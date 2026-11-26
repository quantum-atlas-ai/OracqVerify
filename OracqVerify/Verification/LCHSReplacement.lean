module

public import OracqVerify.Verification.GateEvidence
public import OracqVerify.Verification.LCHSFixtureError

/-! Check two serialized Hamiltonian simulation backends for the same LCHS model. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.LCHS

open Lean RIR Matrix
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.Execution.WorkspaceCP Qatlib.Concepts.LchsSimulation.StaticLchs
open scoped Matrix.Norms.L2Operator

def scaledEntry {source : Program} (evidence : GateEvidence.Certificate source) (scale : ℚ)
    (row col : Bool) : Gaussian :=
  ⟨scale, 0⟩ * evidence.column (GateEvidence.zeroSignal _ col) (GateEvidence.zeroSignal _ row)

structure Entries where
  entry00 : Gaussian
  entry01 : Gaussian
  entry10 : Gaussian
  entry11 : Gaussian

def Entries.get (entries : Entries) (row col : Bool) : Gaussian :=
  if row then (if col then entries.entry11 else entries.entry10)
  else (if col then entries.entry01 else entries.entry00)

def scaledEntries {source : Program} (evidence : GateEvidence.Certificate source) (scale : ℚ) :
    Entries :=
  let r0 := GateEvidence.zeroSignal evidence.trace.wireCount false
  let r1 := GateEvidence.zeroSignal evidence.trace.wireCount true
  let col0 := evidence.columnPair r0 r0 r1
  let col1 := evidence.columnPair r1 r0 r1
  let factor : Gaussian := ⟨scale, 0⟩
  ⟨factor * col0.1, factor * col1.1, factor * col0.2, factor * col1.2⟩

theorem scaledEntries_apply {source : Program} (cert : GateEvidence.Certificate source) (scale : ℚ)
    (row col : Bool) : (scaledEntries cert scale).get row col = scaledEntry cert scale row col := by
  unfold scaledEntries
  simp only [cert.columnPair_eq]
  cases row <;> cases col <;> rfl

def entryLimit (row col : Bool) : ℚ := if row = col then 4515 / 10000 else 129 / 10000

def readScale (source : Program) : Except String ℚ := do
  let entry ← lookupModule source source.entry
  let some (.num value) := entry.attributes.lookup "evolution_alpha"
    | throw "Expected a numeric LCHS evolution_alpha"
  return rationalAngle value

structure ScaledBlock (source : Program) where
  evidence : GateEvidence.Certificate source
  positiveWidth : 0 < evidence.trace.wireCount
  scale : ℚ
  declaredScale : readScale source = .ok scale
  positiveScale : 0 < scale
  smallScale : scale ≤ 1
  entries : Entries
  computed : entries = scaledEntries evidence scale

def certifyScaledBlock (source : Program) : Except String (ScaledBlock source) := do
  let evidence ← GateEvidence.certify source
  let entry ← lookupModule source source.entry
  unless entry.registers == [⟨"target", ⟨.bits, 1⟩⟩, ⟨"signal", ⟨.bits, evidence.trace.wireCount - 1⟩⟩] do
    throw "Expected one LCHS target wire followed by the signal register"
  match declaredScale : readScale source with
  | .error reason => throw reason
  | .ok scale =>
    if positiveWidth : 0 < evidence.trace.wireCount then
      if positiveScale : 0 < scale then
        if smallScale : scale ≤ 1 then
          return ⟨evidence, positiveWidth, scale, declaredScale, positiveScale, smallScale,
            scaledEntries evidence scale, rfl⟩
        else throw "LCHS scaled success block requires scale at most one"
      else throw "LCHS scale must be positive"
    else throw "LCHS target wire is missing"

def ScaledBlock.embed {source : Program} (cert : ScaledBlock source) :
    Bool ↪ Reg cert.evidence.trace.wireCount where
  toFun := GateEvidence.zeroSignal _
  inj' := by
    intro a b same
    exact congrFun same ⟨0, cert.positiveWidth⟩

noncomputable def ScaledBlock.block {source : Program} (cert : ScaledBlock source) :
    Matrix Bool Bool ℂ :=
  (cert.scale : ℝ) • compress (basisFrame cert.embed) cert.evidence.matrix (basisFrame cert.embed)

theorem ScaledBlock.entry_error {source : Program} (cert : ScaledBlock source)
    (row col : Bool) :
    ‖cert.block row col - gaussianComplex (cert.entries.get row col)‖ ≤
      (1 : ℝ) / 10^20 := by
  rw [ScaledBlock.block, Matrix.smul_apply, basisFrame_compress, cert.computed, scaledEntries_apply, scaledEntry, map_mul,
    gaussianComplex_ofReal, ← Complex.real_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by exact_mod_cast cert.positiveScale)]
  have hScale : (cert.scale : ℝ) ≤ 1 := by exact_mod_cast cert.smallScale
  exact (mul_le_of_le_one_left (norm_nonneg _) hScale).trans (cert.evidence.entry_error _ _)

structure BackendCertificate (source : Program) extends ScaledBlock source where
  checked : ∀ row col : Bool,
    GateEvidence.l1 (evolutionEntry row col - entries.get row col) ≤ entryLimit row col

def certifyBackend (source : Program) : Except String (BackendCertificate source) := do
  let corner ← certifyScaledBlock source
  if checked : ∀ row col : Bool,
      GateEvidence.l1 (evolutionEntry row col - corner.entries.get row col) ≤ entryLimit row col then
    return ⟨corner, checked⟩
  else throw "LCHS scaled success block exceeds the error budget"

abbrev BackendCertificate.embed {source : Program} (cert : BackendCertificate source) :=
  cert.toScaledBlock.embed

noncomputable abbrev BackendCertificate.block {source : Program} (cert : BackendCertificate source) :=
  cert.toScaledBlock.block

theorem BackendCertificate.entry_error {source : Program} (cert : BackendCertificate source)
    (row col : Bool) :
    ‖cert.block row col - gaussianComplex (cert.entries.get row col)‖ ≤
      (1 : ℝ) / 10^20 :=
  cert.toScaledBlock.entry_error row col

private theorem BackendCertificate.continuum_error {source : Program} (cert : BackendCertificate source) :
    ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - cert.block‖ ≤ (47 : ℝ) / 100 := by
  have entry (row col : Bool) :
      ‖(evolutionTaylor - cert.block) row col‖ ≤ (entryLimit row col : ℝ) + 1 / 10^20 := by
    rw [Matrix.sub_apply, evolutionTaylor_entry]
    have checked := (GateEvidence.norm_le_l1
      (evolutionEntry row col - cert.entries.get row col)).trans
      (show (GateEvidence.l1 _ : ℝ) ≤ (entryLimit row col : ℝ) by exact_mod_cast cert.checked row col)
    rw [map_sub] at checked
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add checked ((norm_sub_rev ..).le.trans (cert.entry_error row col)))
  have bound : ‖evolutionTaylor - cert.block‖ ≤ (465 : ℝ) / 1000 := by
    refine (boolMatrixNorm _ (diag := 452 / 1000) (off := 13 / 1000) (by norm_num) (by norm_num)
      ?_ ?_).trans (by norm_num)
    · intro i
      exact (entry i i).trans (by norm_num [entryLimit])
    · intro i
      cases i
      · exact (entry false true).trans (by norm_num [entryLimit])
      · exact (entry true false).trans (by norm_num [entryLimit])
  calc
    _ = ‖(staticNonunitaryEvolution sampleL sampleH (1 / 8) - evolutionTaylor) +
        (evolutionTaylor - cert.block)‖ := by congr 1; abel
    _ ≤ (343 : ℝ) / 98304 + 465 / 1000 :=
      (norm_add_le ..).trans (add_le_add evolutionTaylor_remainder bound)
    _ ≤ _ := by norm_num

theorem BackendCertificate.sound {source : Program} (cert : BackendCertificate source) :
    source.matrix (fun _ => none) = .ok ⟨cert.evidence.trace.wireCount, cert.evidence.matrix⟩ ∧
      BlockEncoding (staticNonunitaryEvolution sampleL sampleH (1 / 8)) cert.evidence.matrix
        (basisFrame cert.embed) (basisFrame cert.embed) (cert.scale : ℝ) ((47 : ℝ) / 100) := by
  exact ⟨cert.evidence.sound.1, cert.evidence.sound.2, basisFrame_isIsometry _, basisFrame_isIsometry _,
    by exact_mod_cast cert.positiveScale, by norm_num, cert.continuum_error⟩

structure Replacement (baseline candidate : Program) where
  first : BackendCertificate baseline
  second : BackendCertificate candidate
  checked : ∀ row col : Bool,
    GateEvidence.l1 (first.entries.get row col -
      second.entries.get row col) ≤ 249 / 1000000

def checkReplacement (baseline candidate : Program) : Except String (Replacement baseline candidate) := do
  let first ← certifyBackend baseline
  let second ← certifyBackend candidate
  if checked : ∀ row col : Bool, GateEvidence.l1 (first.entries.get row col -
      second.entries.get row col) ≤ 249 / 1000000 then
    return ⟨first, second, checked⟩
  else throw "LCHS replacement exceeds the backend discrepancy budget"

/-- Independently certified success blocks can be compared despite different scales and workspaces. -/
theorem Replacement.agreement {baseline candidate : Program} (cert : Replacement baseline candidate) :
    ‖cert.first.block - cert.second.block‖ ≤ (1 : ℝ) / 1000 := by
  have bound := norm_bool_matrix_le (cert.first.block - cert.second.block)
    (b := (1 : ℝ) / 4000) (by norm_num) (fun row col => by
      rw [Matrix.sub_apply]
      have discrepancy := (GateEvidence.norm_le_l1
        (cert.first.entries.get row col -
          cert.second.entries.get row col)).trans
        (show (GateEvidence.l1 _ : ℝ) ≤ 249 / 1000000 by
          have numeric := (Rat.cast_le (K := ℝ)).mpr (cert.checked row col)
          norm_num at numeric ⊢
          exact numeric)
      rw [map_sub] at discrepancy
      have first := cert.first.entry_error row col
      have second := (norm_sub_rev ..).le.trans (cert.second.entry_error row col)
      have assembled := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add first ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
          (add_le_add discrepancy second)))
      exact assembled.trans (by norm_num))
  exact bound.trans (by norm_num)

end OracqVerify.Verification.LCHS
