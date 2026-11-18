module

public import OracqVerify.OpenBell
public import Qatlib.Foundations.QueryWordCore.Circuit

/-! The decoded Open Bell fixture evaluated in Qatlib's complex circuit semantics. -/

set_option warningAsError true

public section

namespace OracqVerify.OpenBell

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

private abbrev WireBasis := Bool × Bool

private noncomputable def lowerGate (gate : Gate) : Option (Step WireBasis) :=
  match gate with
  | .h wire =>
    some (.gate (if wire = 0 then TensorGate Hadamard 1 else TensorGate 1 Hadamard))
  | .cx control target =>
    if control = target then none
    else if control = 0 then some (.gate CNOT)
    else some (.gate (Matrix.reindex (Equiv.prodComm Bool Bool) (Equiv.prodComm Bool Bool) CNOT))

/-- Translate decoded gates into Qatlib's circuit over the two wire bits in wire order. -/
noncomputable def qatlibCircuit (gates : List Gate) : Option (Circuit (Bool × Bool)) :=
  gates.mapM lowerGate

/-- The serialized Bell program has one wire-zero Hadamard followed by a controlled-X. -/
noncomputable def bellWord : Circuit (Bool × Bool) :=
  [.gate (TensorGate Hadamard 1), .gate CNOT]

/-- The Qatlib word is obtained from the same decoded fixture used for strict resource counts. -/
theorem exported_qatlib_word : qatlibCircuit exportedProgram = some bellWord := by
  rw [exported_program]
  rfl

/-- Running the decoded word from zero in Qatlib gives the Bell amplitudes on the physical wires. -/
theorem exported_qatlib_bell (oracle : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Run oracle bellWord (Ket (false, false)) =
      fun bits => if bits.1 = bits.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0 := by
  rw [← tensorState_ket_ket]
  change ApplyGate CNOT (ApplyGate (TensorGate Hadamard 1) (TensorState (Ket false) (Ket false))) = _
  rw [applyGate_tensorGate, applyGate_hadamard_ket_false, applyGate_one]
  funext bits
  rw [CNOT, applyGate_permMatrix cnotFlip_involutive]
  rcases bits with ⟨control, target⟩
  cases control <;> cases target <;>
    simp [cnotFlip, TensorState, Plus, hadamard_apply_false, Ket]

/-- The decoded Qatlib word uses zero queries and two explicit matrix instructions. -/
theorem exported_qatlib_counts : QueryCount bellWord = 0 ∧ GateCount bellWord = 2 := by
  simp [bellWord]

/-- One word from the exported RIR witnesses both Qatlib semantics and matrix-word costs. -/
theorem exported_qatlib_evidence :
    ∃ word, qatlibCircuit exportedProgram = some word ∧
      (∀ oracle, Run oracle word (Ket (false, false)) =
        fun bits => if bits.1 = bits.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0) ∧
      QueryCount word = 0 ∧ GateCount word = 2 :=
  ⟨bellWord, exported_qatlib_word, exported_qatlib_bell, exported_qatlib_counts⟩

end OracqVerify.OpenBell
