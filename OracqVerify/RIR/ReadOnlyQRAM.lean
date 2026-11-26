module

public import Qatlib.Foundations.PureStateMath.Qubit

/-! The coherent XOR semantics of a RIR `Load` against a fixed QRAM bank. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR.ReadOnlyQRAM

open Qatlib.Foundations.PureStateMath

/-- A read-only snapshot associates a data word with each address. -/
abbrev Bank (addressWidth dataWidth : Nat) : Type := Reg addressWidth → Reg dataWidth

/-- The computational basis of the address and data registers, in that order. -/
abbrev LoadBasis (addressWidth dataWidth : Nat) : Type := Reg addressWidth × Reg dataWidth

/-- Preserve the address and XOR the selected cell into the existing data word. -/
def loadBasis {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth)
    (input : LoadBasis addressWidth dataWidth) : LoadBasis addressWidth dataWidth :=
  (input.1, fun bit => input.2 bit ^^ bank input.1 bit)

/-- Loading the same unchanged bank twice restores the data for every basis input. -/
theorem loadBasis_involutive {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth) :
    Function.Involutive (loadBasis bank) := by
  intro input
  apply Prod.ext
  · rfl
  · funext bit
    change ((input.2 bit ^^ bank input.1 bit) ^^ bank input.1 bit) = input.2 bit
    cases input.2 bit <;> cases bank input.1 bit <;> rfl

/-- The coherent operation represented as a permutation matrix in Qatlib. -/
noncomputable def loadMatrix {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth) :
    Matrix (LoadBasis addressWidth dataWidth) (LoadBasis addressWidth dataWidth) ℂ :=
  permMatrix (loadBasis bank)

/-- Matrix action on a basis state agrees with the register-level XOR update. -/
theorem loadMatrix_ket {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth)
    (input : LoadBasis addressWidth dataWidth) :
    ApplyGate (loadMatrix bank) (Ket input) = Ket (loadBasis bank input) :=
  applyGate_permMatrix_ket (loadBasis_involutive bank) input

/-- A coherent load against a fixed snapshot is unitary. -/
theorem loadMatrix_unitary {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth) :
    loadMatrix bank ∈ Matrix.unitaryGroup (LoadBasis addressWidth dataWidth) ℂ :=
  permMatrix_unitary (loadBasis_involutive bank)

/-- The same fixed-bank load is its own inverse on the entire quantum state space. -/
theorem loadMatrix_mul_self {addressWidth dataWidth : Nat} (bank : Bank addressWidth dataWidth) :
    loadMatrix bank * loadMatrix bank = 1 :=
  permMatrix_mul_self (loadBasis_involutive bank)

private def firstBitBank (address : Reg 1) : Reg 2 :=
  fun bit => address 0 && bit == 0

-- A nonzero data word is updated by XOR, including when the input bit is already set.
example :
    (loadBasis firstBitBank (fun _ => true, fun _ => true)).2 0 = false ∧
    (loadBasis firstBitBank (fun _ => true, fun _ => true)).2 1 = true := by decide

end OracqVerify.RIR.ReadOnlyQRAM
