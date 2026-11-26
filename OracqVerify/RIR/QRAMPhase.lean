module

public import OracqVerify.RIR.GateAction

/-! Exact compute–phase–uncompute with a coherent read from one fixed bank. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath Matrix

private theorem permMatrix_diagonal_transfer {I : Type} [Fintype I] [DecidableEq I]
    (f : I → I) (hf : Function.Involutive f) (phase : I → ℂ) :
    permMatrix f * diagonal phase * permMatrix f = diagonal (phase ∘ f) := by
  have h : permMatrix f * diagonal phase = diagonal (phase ∘ f) * permMatrix f := by
    ext r c
    simp only [mul_diagonal, diagonal_mul, permMatrix, Matrix.of_apply, Function.comp_apply]
    split
    · rename_i he
      simp [he, hf c]
    · simp
  rw [h, mul_assoc, permMatrix_mul_self hf, mul_one]

theorem atWire_z (wireCount : Nat) (wire : Fin wireCount) :
    atWire wire PauliZ = diagonal (fun row => if row wire then (-1 : ℂ) else 1) := by
  ext row col
  by_cases same : row = col
  · subst col
    simp [atWire, PauliZ]
  · rw [diagonal_apply_ne _ same]
    unfold atWire
    split
    · rename_i spectators
      have bit : row wire ≠ col wire := by
        intro h
        apply same
        funext i
        by_cases hi : i = wire
        · simpa [hi] using h
        · exact spectators i hi
      rw [PauliZ, diagonal_apply_ne _ bit]
    · rfl

/-- The three resolved instructions of a phase read using one bit of the data word. -/
@[expose] def qramPhaseWord {n : Nat} (read : ResolvedRead n) (address data : List Nat)
    (bit : Fin read.bank.type.dataWidth) : ResolvedProgram :=
  let load := ResolvedInstruction.load read.bank address data
  ⟨n, [load, .unary .z [(read.data bit).val], load]⟩

set_option maxHeartbeats 800000 in
/-- The two reads restore the entire computational basis state. Their effect is a
sign determined by the selected bit after the first read. This is a matrix identity. -/
theorem qramPhaseWord_matrix {n : Nat} (read : ResolvedRead n) (address data : List Nat)
    (decode : ResolvedRead.create n read.bank address data = .ok read)
    (snapshot : Snapshot) (bank : ReadOnlyQRAM.Bank read.bank.type.addressWidth read.bank.type.dataWidth)
    (supplied : snapshot read.bank = some bank) (bit : Fin read.bank.type.dataWidth) :
    (qramPhaseWord read address data bit).matrix snapshot = .ok
      (diagonal fun state => if loadAtBasis read.address read.data bank state (read.data bit)
        then (-1 : ℂ) else 1) := by
  let f := loadAtBasis read.address read.data bank
  have load : (ResolvedInstruction.load read.bank address data).matrix n snapshot = .ok (permMatrix f) := by
    simp [ResolvedInstruction.matrix, ResolvedInstruction.loadMatrix, decode, ResolvedRead.matrix,
      supplied, f, Bind.bind, Except.bind]
  have lowered : GateAction.lower n false (.unary .z [(read.data bit).val]) =
      .ok (.unary .z (read.data bit) false) := by simp [GateAction.lower, (read.data bit).isLt]
  have phase : (ResolvedInstruction.unary .z [(read.data bit).val]).matrix n snapshot =
      .ok (atWire (read.data bit) PauliZ) := GateAction.lower_matrix snapshot lowered
  change (do
    let matrices ← [ResolvedInstruction.load read.bank address data,
      .unary .z [(read.data bit).val], .load read.bank address data].mapM
      (ResolvedInstruction.matrix n snapshot)
    pure (wordMatrix matrices)) = _
  simp only [List.mapM_cons, load, phase, List.mapM_nil,
    Bind.bind, Except.bind, Pure.pure, Except.pure, wordMatrix]
  rw [atWire_z, one_mul]
  exact congrArg Except.ok (permMatrix_diagonal_transfer f (loadAt_involutive _ _ bank read.disjoint) _)

/-- On clean workspace the phase reads the requested bank bit at the original ordered address. -/
theorem qramPhaseWord_clean_diagonal {n : Nat} (read : ResolvedRead n)
    (bank : ReadOnlyQRAM.Bank read.bank.type.addressWidth read.bank.type.dataWidth)
    (state : Reg n) (bit : Fin read.bank.type.dataWidth) (clean : state (read.data bit) = false) :
    loadAtBasis read.address read.data bank state (read.data bit) = bank (state ∘ read.address) bit := by
  rw [loadAt_data]
  simp [ReadOnlyQRAM.loadBasis, clean]

end OracqVerify.RIR
