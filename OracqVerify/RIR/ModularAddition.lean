module

public import OracqVerify.RIR.QRAM

/-! The reversible modular-addition primitive on an ordered register view. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix Classical

/-- The packed word follows the little-endian coordinate convention of the register view. -/
def unsignedWord (width : Nat) : Reg width ≃ BitVec width :=
  (orderedBitsIndex width).trans ⟨BitVec.ofFin, BitVec.toFin, by intro x; rfl, BitVec.ofFin_toFin⟩

/-- Write a modular sum into the target view while preserving every spectator coordinate. -/
noncomputable def addAtBasis {n w : Nat} (view : View n w) (amount : BitVec w) (state : Reg n) : Reg n :=
  let sum := (unsignedWord w).symm (unsignedWord w (state ∘ view) + amount)
  fun wire => if h : ∃ i, view i = wire then sum (Classical.choose h) else state wire

theorem addAtBasis_read {n w : Nat} (view : View n w) (amount : BitVec w) (state : Reg n) :
    addAtBasis view amount state ∘ view = (unsignedWord w).symm (unsignedWord w (state ∘ view) + amount) := by
  funext i
  let h : ∃ j, view j = view i := ⟨i, rfl⟩
  have hj := view.injective (Classical.choose_spec h)
  simp only [Function.comp_apply, addAtBasis, dite_eq_left h, hj]

theorem addAtBasis_other {n w : Nat} (view : View n w) (amount : BitVec w) (state : Reg n)
    (wire : Fin n) (other : ¬ ∃ i, view i = wire) : addAtBasis view amount state wire = state wire := by
  simp [addAtBasis, other]

/-- Subtracting the same word in the same ordered wires restores the entire input. -/
theorem addAtBasis_inverse {n w : Nat} (view : View n w) (amount : BitVec w) :
    Function.LeftInverse (addAtBasis view (-amount)) (addAtBasis view amount) := by
  intro state
  funext wire
  by_cases onView : ∃ i, view i = wire
  · obtain ⟨i, rfl⟩ := onView
    change ((addAtBasis view (-amount) (addAtBasis view amount state)) ∘ view) i = (state ∘ view) i
    rw [addAtBasis_read, addAtBasis_read, Equiv.apply_symm_apply, ← BitVec.sub_eq_add_neg,
      BitVec.add_sub_cancel, Equiv.symm_apply_apply]
  · rw [addAtBasis_other _ _ _ _ onView, addAtBasis_other _ _ _ _ onView]

private theorem permutation_unitary {I : Type} [Fintype I] [DecidableEq I] (f : I → I)
    (injective : Function.Injective f) : permMatrix f ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext row col
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (f col)]
  · by_cases same : row = col
    · subst col
      simp
    · have different : f col ≠ f row := fun h => same (injective h.symm)
      simp [same, different]
  · intro x _ h
    simp [h]
  · simp

/-- The permutation of basis states determined by addition is unitary. -/
theorem addAtBasis_unitary {n w : Nat} (view : View n w) (amount : BitVec w) :
    permMatrix (addAtBasis view amount) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  permutation_unitary _ (addAtBasis_inverse view amount).injective

/-- Taking the adjoint of the placed permutation subtracts the same word. -/
theorem addAtBasis_adjoint {n w : Nat} (view : View n w) (amount : BitVec w) :
    (permMatrix (addAtBasis view amount))ᴴ = permMatrix (addAtBasis view (-amount)) := by
  ext row col
  have hInverse := addAtBasis_inverse view amount
  have hRight : Function.LeftInverse (addAtBasis view amount) (addAtBasis view (-amount)) := by
    simpa using addAtBasis_inverse view (-amount)
  have coords : col = addAtBasis view amount row ↔ row = addAtBasis view (-amount) col := by
    constructor
    · intro h
      rw [h, hInverse]
    · intro h
      rw [h, hRight]
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  by_cases h : col = addAtBasis view amount row
  · rw [ite_eq_left h, ite_eq_left (coords.mp h), map_one]
  · have h' : row ≠ addAtBasis view (-amount) col := fun eq => h (coords.mpr eq)
    rw [ite_eq_right h, ite_eq_right h', map_zero]

/-- Interpret a resolved constant addition in the ordered physical wires of its unsigned operand. -/
noncomputable def addConstMatrix (n : Nat) (wires : List Nat) (amount : Nat) :
    Except String (Matrix (Reg n) (Reg n) ℂ) := do
  let view ← View.ofWires n wires.length wires
  return permMatrix (addAtBasis view (BitVec.ofNat wires.length amount))

end OracqVerify.RIR
