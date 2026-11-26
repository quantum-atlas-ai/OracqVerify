module

public import OracqVerify.RIR.GateAction

/-! Compute, select a single-wire rotation from memory, and uncompute on arbitrary states. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Classical Matrix

theorem loadAt_updateBit {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (wire : Fin n)
    (offAddress : ∀ i, wire ≠ address i) (offData : ∀ j, wire ≠ data j)
    (state : Reg n) (bit : Bool) :
    loadAtBasis address data bank (updateBit state wire bit) =
      updateBit (loadAtBasis address data bank state) wire bit := by
  have sameAddress : updateBit state wire bit ∘ address = state ∘ address := by
    funext i
    simp [updateBit, Function.update_of_ne (offAddress i).symm]
  funext k
  by_cases onData : ∃ j, data j = k
  · obtain ⟨j, rfl⟩ := onData
    have unchanged : updateBit (loadAtBasis address data bank state) wire bit (data j) =
        loadAtBasis address data bank state (data j) := by
      simp [updateBit, Function.update_of_ne (offData j).symm]
    rw [loadAt_data, unchanged, loadAt_data]
    rw [sameAddress]
    simp [ReadOnlyQRAM.loadBasis, updateBit, Function.update_of_ne (offData j).symm]
  · rw [loadAt_other _ _ _ _ _ onData]
    by_cases atWire : k = wire
    · subst k
      simp [updateBit]
    · simp [updateBit, Function.update_of_ne atWire, loadAt_other _ _ _ _ _ onData]

/-- Apply a different single-wire gate for each data word on the row's ordered data view. -/
noncomputable def dataSelectedWire {n d : Nat} (data : View n d) (wire : Fin n)
    (gates : Reg d → Matrix Bool Bool ℂ) : WireMatrix n :=
  fun row col => atWire wire (gates (row ∘ data)) row col

theorem dataSelectedWire_apply {n d : Nat} (data : View n d) (wire : Fin n)
    (gates : Reg d → Matrix Bool Bool ℂ) (ψ : QState (Reg n)) (row : Reg n) :
    ApplyGate (dataSelectedWire data wire gates) ψ row =
      gates (row ∘ data) (row wire) false * ψ (updateBit row wire false) +
        gates (row ∘ data) (row wire) true * ψ (updateBit row wire true) :=
  atWire_apply wire (gates (row ∘ data)) ψ row

private theorem updateBit_spectators {n d : Nat} (data : View n d) (wire : Fin n)
    (offData : ∀ i, wire ≠ data i) (row : Reg n) (b : Bool) :
    updateBit row wire b ∘ data = row ∘ data := by
  funext i
  simp [updateBit, Function.update_of_ne (offData i).symm]

theorem addAt_updateBit {n w : Nat} (view : View n w) (amount : BitVec w) (wire : Fin n)
    (offView : ∀ i, wire ≠ view i) (state : Reg n) (bit : Bool) :
    addAtBasis view amount (updateBit state wire bit) = updateBit (addAtBasis view amount state) wire bit := by
  funext k
  by_cases onView : ∃ i, view i = k
  · obtain ⟨i, rfl⟩ := onView
    have unchanged : updateBit (addAtBasis view amount state) wire bit (view i) =
        addAtBasis view amount state (view i) := by
      simp [updateBit, Function.update_of_ne (offView i).symm]
    rw [unchanged]
    change (addAtBasis view amount (updateBit state wire bit) ∘ view) i =
      (addAtBasis view amount state ∘ view) i
    rw [addAtBasis_read, addAtBasis_read, updateBit_spectators view wire offView]
  · rw [addAtBasis_other _ _ _ _ onView]
    by_cases onWire : k = wire
    · subst k
      simp [updateBit]
    · simp [updateBit, Function.update_of_ne onWire, addAtBasis_other _ _ _ _ onView]

theorem dataSelectedWire_mul {n d : Nat} (data : View n d) (wire : Fin n)
    (offData : ∀ i, wire ≠ data i) (u v : Reg d → Matrix Bool Bool ℂ) :
    dataSelectedWire data wire u * dataSelectedWire data wire v =
      dataSelectedWire data wire (fun bits => u bits * v bits) := by
  ext row col
  simp only [← applyGate_eq_mulVec_ket _ col row]
  simp only [ApplyGate, ← Matrix.mulVec_mulVec]
  change ApplyGate (dataSelectedWire data wire u) (ApplyGate (dataSelectedWire data wire v) (Ket col)) row =
    ApplyGate (dataSelectedWire data wire (fun bits => u bits * v bits)) (Ket col) row
  simp only [dataSelectedWire_apply, updateBit_spectators data wire offData, Matrix.mul_apply, Fintype.sum_bool]
  simp only [updateBit, Function.update_self, Function.update_idem]
  ring

private theorem dataSelectedWire_one {n d : Nat} (data : View n d) (wire : Fin n) :
    dataSelectedWire data wire (fun _ => 1) = 1 := by
  ext row col
  by_cases h : ∀ i : Fin n, i ≠ wire → row i = col i
  · have hEq : row = col ↔ row wire = col wire := by
      refine ⟨fun eq => congrFun eq wire, fun eq => ?_⟩
      funext i
      by_cases hi : i = wire
      · simpa [hi] using eq
      · exact h i hi
    change atWire wire (1 : Matrix Bool Bool ℂ) row col = _
    rw [atWire, ite_eq_left h]
    simp only [Matrix.one_apply, hEq]
  · have ne : row ≠ col := fun eq => h (by simp [eq])
    simp [dataSelectedWire, atWire, h, ne]

/-- A coherent guard on the data word selects a rotation on a disjoint wire. -/
theorem controlled_data_rotation {n d : Nat} (data : View n d) (wire : Fin n)
    (offData : ∀ i, wire ≠ data i) (active : Reg d → Prop) [DecidablePred active] (angle : ℝ) :
    controlledMatrix (fun row : Reg n => active (row ∘ data)) (atWire wire (rotationY angle)) =
      dataSelectedWire data wire (fun bits => if active bits then rotationY angle else 1) := by
  ext row col
  by_cases h : ∀ i : Fin n, i ≠ wire → row i = col i
  · have same : row ∘ data = col ∘ data := funext fun i => h (data i) (offData i).symm
    by_cases enabled : active (row ∘ data)
    · have colEnabled : active (col ∘ data) := same ▸ enabled
      simp [controlledMatrix, dataSelectedWire, enabled, colEnabled]
    · have hOne := congrArg (fun m : WireMatrix n => m row col) (dataSelectedWire_one data wire)
      simpa [controlledMatrix, dataSelectedWire, enabled] using hOne.symm
  · have ne : row ≠ col := fun eq => h (by simp [eq])
    simp [controlledMatrix, dataSelectedWire, atWire, h, ne]

/-- A guard on one angle bit selects the rotation on a disjoint wire. -/
theorem controlled_bit_rotation {n d : Nat} (data : View n d) (wire : Fin n)
    (bit : Fin d) (offData : wire ≠ data bit) (angle : ℝ) :
    controlledMatrix (fun row : Reg n => row (data bit) = true) (atWire wire (rotationY angle)) =
      dataSelectedWire data wire (fun bits => if bits bit then rotationY angle else 1) := by
  ext row col
  by_cases h : ∀ i : Fin n, i ≠ wire → row i = col i
  · have same := h (data bit) offData.symm
    cases hb : row (data bit)
    · have hOne := congrArg (fun m : WireMatrix n => m row col) (dataSelectedWire_one data wire)
      change atWire wire (1 : Matrix Bool Bool ℂ) row col = _ at hOne
      simpa [controlledMatrix, dataSelectedWire, hb] using hOne.symm
    · have hc : col (data bit) = true := same.symm.trans hb
      simp [controlledMatrix, dataSelectedWire, hb, hc]
  · have ne : row ≠ col := fun eq => h (by simp [eq])
    simp [controlledMatrix, dataSelectedWire, atWire, h, ne]

theorem rotationY_zero : rotationY 0 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [rotationY]

theorem rotationY_add (a b : ℝ) : rotationY (a + b) = rotationY a * rotationY b := by
  ext i j
  cases i <;> cases j <;>
    simp [rotationY, Matrix.mul_apply, add_div, Real.cos_add, Real.sin_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add] <;> ring

/-- Compose any list of bit-controlled rotations on the same target using the exact
serialized angles. This is a matrix identity on all input states. -/
theorem bitRotations_matrix {n d : Nat} (data : View n d) (wire : Fin n)
    (offData : ∀ i, wire ≠ data i) (steps : List (Fin d × ℝ)) :
    wordMatrix (steps.map fun (bit, angle) =>
      controlledMatrix (fun row : Reg n => row (data bit) = true) (atWire wire (rotationY angle))) =
      dataSelectedWire data wire (fun bits =>
        rotationY ((steps.map fun (bit, angle) => if bits bit then angle else 0).sum)) := by
  induction steps with
  | nil => simp [wordMatrix, rotationY_zero, dataSelectedWire_one]
  | cons head tail ih =>
    obtain ⟨bit, angle⟩ := head
    simp only [List.map_cons, wordMatrix, ih, controlled_bit_rotation data wire bit (offData bit),
      dataSelectedWire_mul data wire offData, List.sum_cons]
    congr 1
    funext bits
    cases hb : bits bit
    · simp
    · simp only [ite_true]
      rw [← rotationY_add, add_comm]

/-- A permutation sends the amplitude at an output row to the amplitude at its inverse image. -/
theorem applyGate_permMatrix_inverse {I : Type} [Fintype I] [DecidableEq I]
    {f g : I → I} (left : Function.LeftInverse g f) (right : Function.RightInverse g f)
    (ψ : QState I) (row : I) : ApplyGate (permMatrix f) ψ row = ψ (g row) := by
  simp only [ApplyGate, permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (g row)]
  · simp [right row]
  · intro col _ different
    have ne : row ≠ f col := fun eq => different (by rw [eq, left col])
    simp [ne]
  · simp

theorem permMatrix_comp {I : Type} [Fintype I] [DecidableEq I] (f g : I → I) :
    permMatrix g * permMatrix f = permMatrix (g ∘ f) := by
  ext row col
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (f col)]
  · simp
  · intro i _ different
    simp [different]
  · simp

/-- Compute and uncompute a reversible address map around a one-wire operation. The map
can change all other wires. It preserves the target and does not use it as an input. -/
theorem perm_compute_wire_uncompute {n : Nat} {f g : Reg n → Reg n}
    (left : Function.LeftInverse g f) (right : Function.RightInverse g f) (wire : Fin n)
    (spectator : ∀ row, f row wire = row wire)
    (commutes : ∀ row bit, f (updateBit row wire bit) = updateBit (f row) wire bit)
    (u : WireMatrix n) (gate : Reg n → Matrix Bool Bool ℂ)
    (pointwise : ∀ ψ row, ApplyGate u ψ row =
      gate row (row wire) false * ψ (updateBit row wire false) +
        gate row (row wire) true * ψ (updateBit row wire true))
    (ψ : QState (Reg n)) (row : Reg n) :
    ApplyGate (permMatrix g * u * permMatrix f) ψ row =
      gate (f row) (row wire) false * ψ (updateBit row wire false) +
        gate (f row) (row wire) true * ψ (updateBit row wire true) := by
  rw [mul_assoc]
  simp only [ApplyGate, ← mulVec_mulVec]
  change ApplyGate (permMatrix g) (ApplyGate u (ApplyGate (permMatrix f) ψ)) row = _
  rw [applyGate_permMatrix_inverse right left, pointwise,
    applyGate_permMatrix_inverse left right, applyGate_permMatrix_inverse left right,
    ← commutes, ← commutes, left, left, spectator]

/-- Conjugating a data-selected gate by a coherent read preserves the workspace and selects
its action by the word after the read, for arbitrary input amplitudes. -/
theorem load_dataSelectedWire_unload {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (disjoint : DisjointViews address data) (wire : Fin n)
    (offAddress : ∀ i, wire ≠ address i) (offData : ∀ j, wire ≠ data j)
    (gates : Reg d → Matrix Bool Bool ℂ) (ψ : QState (Reg n)) (row : Reg n) :
    let load := permMatrix (loadAtBasis address data bank)
    let gate := gates (ReadOnlyQRAM.loadBasis bank (row ∘ address, row ∘ data)).2
    ApplyGate (load * dataSelectedWire data wire gates * load) ψ row =
      gate (row wire) false * ψ (updateBit row wire false) +
        gate (row wire) true * ψ (updateBit row wire true) := by
  let f := loadAtBasis address data bank
  have hf : Function.Involutive f := loadAt_involutive address data bank disjoint
  have spectator (state : Reg n) : f state wire = state wire :=
    loadAt_other address data bank state wire (fun h =>
      let ⟨j, eq⟩ := h
      offData j eq.symm)
  have h := perm_compute_wire_uncompute hf hf wire spectator
    (loadAt_updateBit address data bank wire offAddress offData) (dataSelectedWire data wire gates)
    (fun state => gates (state ∘ data)) (dataSelectedWire_apply data wire gates) ψ row
  have readData : f row ∘ data = (ReadOnlyQRAM.loadBasis bank (row ∘ address, row ∘ data)).2 := by
    funext j
    exact loadAt_data address data bank row j
  simpa only [readData] using h

end OracqVerify.RIR
