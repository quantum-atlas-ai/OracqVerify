module

public import OracqVerify.RIR.ScopedLink
public import OracqVerify.RIR.QRAMPhase

/-! A clean scoped oracle realized by a QRAM read, a phase, and an uncomputation. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath Matrix

/-- A read–Z–read body whose data bit is local implements a phase oracle on
its public wires. The result uses the snapshot in the module's bank frame. -/
theorem scopedQramPhase_interpret (m : ScopedModule) (read : ResolvedRead m.width)
    (address data : List Nat) (decode : ResolvedRead.create m.width read.bank address data = .ok read)
    (bit : Fin read.bank.type.dataWidth) (localBit : Fin m.localWires)
    (privateBit : read.data bit = Fin.natAdd m.publicWires localBit)
    (body : m.body = some (qramPhaseWord read address data bit).instructions)
    (environment : ScopedEnvironment) (snapshot : Snapshot)
    (bank : ReadOnlyQRAM.Bank read.bank.type.addressWidth read.bank.type.dataWidth)
    (supplied : snapshot read.bank = some bank) :
    m.interpret environment snapshot = .ok
      (diagonal fun state => if bank ((appendZero m.publicWires m.localWires state) ∘ read.address) bit
        then (-1 : ℂ) else 1) := by
  let coeff := fun state => if loadAtBasis read.address read.data bank state (read.data bit)
    then (-1 : ℂ) else 1
  let u := diagonal coeff
  have bodyMatrix : m.bodyMatrix snapshot (environment.atCall m.width snapshot) = .ok u := by
    unfold ScopedModule.bodyMatrix
    rw [body]
    exact qramPhaseWord_matrix read address data decode snapshot bank supplied bit
  have unitary : u ∈ Matrix.unitaryGroup (Reg m.width) ℂ := by
    apply diagonal_mem_unitaryGroup
    intro state
    unfold coeff
    split <;> simp
  have clean : m.Clean u := by
    apply (m.clean_iff_zero_off_frame u).mpr
    intro row col outside
    exact diagonal_apply_ne coeff (outside col)
  rw [ScopedModule.Certificate.interpret ⟨bodyMatrix, unitary, clean⟩]
  congr 1
  ext row col
  rw [ScopedModule.publicMatrix, ScopedModule.frame, basisFrame_compress]
  by_cases same : row = col
  · subst col
    simp only [u, diagonal_apply_eq, coeff]
    rw [qramPhaseWord_clean_diagonal read bank _ bit (by rw [privateBit, appendZero_local])]
  · unfold u
    rw [diagonal_apply_ne _ same, diagonal_apply_ne _ (fun eq => same (Function.Embedding.injective _ eq))]

end OracqVerify.RIR
