module

public import OracqVerify.RIR.Resolve
public import OracqVerify.RIR.ReadOnlyQRAM

/-! Embed a resolved coherent QRAM read into the entry's wire basis. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

/-- A view identifies each local bit with a distinct entry wire. -/
abbrev View (wireCount width : Nat) := Fin width ↪ Fin wireCount

/-- Convert an ordered register to the little-endian integer used by Oracq words and addresses. -/
def orderedBitsIndex : (width : Nat) → Reg width ≃ Fin (2 ^ width)
  | 0 => bitVecEquiv 0
  | width + 1 =>
    (regSuccEquiv width).trans
      ((Equiv.prodCongr (orderedBitsIndex width) boolEquivFin2).trans
        ((Equiv.prodComm _ _).trans
          (finProdFinEquiv.trans (finCongr (by rw [Nat.pow_succ, Nat.mul_comm])))))

theorem orderedBitsIndex_succ (width : Nat) (address : Reg (width + 1)) :
    (orderedBitsIndex (width + 1) address).val =
      (if address (Fin.last width) then 2 ^ width else 0) +
        (orderedBitsIndex width (fun i => address i.castSucc)).val := by
  have hLast : Fin.natAdd width (0 : Fin 1) = Fin.last width := rfl
  have hLower (i : Fin width) : Fin.castAdd 1 i = i.castSucc := rfl
  simp [orderedBitsIndex, regSuccEquiv, Fin.succFunEquiv, finProdFinEquiv, boolEquivFin2, hLast, hLower]
  split <;> simp [Nat.add_comm]

/-- Build a typed view by checking the resolved wire list in its original order. -/
def View.ofWires (wireCount width : Nat) (wires : List Nat) :
    Except String (View wireCount width) := do
  if hLength : wires.length = width then
    let index (i : Fin width) := wires[i.cast hLength.symm]
    if hBounds : ∀ i : Fin width, index i < wireCount then
      let wire (i : Fin width) : Fin wireCount := ⟨index i, hBounds i⟩
      if hDistinct : ∀ i j : Fin width, wire i = wire j → i = j then
        return ⟨wire, fun i j h => hDistinct i j h⟩
      else throw "View repeats an entry wire"
    else throw "View is outside the entry wire range"
  else throw "Resolved view has the wrong width"

/-- Address and data views that can be used simultaneously. -/
def DisjointViews {wireCount a d : Nat} (address : View wireCount a) (data : View wireCount d) :
    Prop :=
  ∀ i j, address i ≠ data j

/-- The result on the full basis, leaving wires outside the data view untouched. -/
noncomputable def loadAtBasis {wireCount a d : Nat}
    (address : View wireCount a) (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d)
    (state : Reg wireCount) : Reg wireCount := fun wire =>
  if h : ∃ j, data j = wire then
    (ReadOnlyQRAM.loadBasis bank (state ∘ address, state ∘ data)).2 (Classical.choose h)
  else state wire

/-- Reading the data view after the load yields the same XOR update as the stand-alone bank. -/
theorem loadAt_data {wireCount a d : Nat} (address : View wireCount a)
    (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d) (state : Reg wireCount)
    (j : Fin d) :
    loadAtBasis address data bank state (data j) =
      (ReadOnlyQRAM.loadBasis bank (state ∘ address, state ∘ data)).2 j := by
  let h : ∃ k, data k = data j := ⟨j, rfl⟩
  have hj := data.injective (Classical.choose_spec h)
  unfold loadAtBasis
  rw [dite_eq_left h, hj]

/-- A disjoint address view is unchanged, including for views that cross register boundaries. -/
theorem loadAt_address {wireCount a d : Nat} (address : View wireCount a)
    (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d)
    (hDisjoint : DisjointViews address data) (state : Reg wireCount) :
    loadAtBasis address data bank state ∘ address = state ∘ address := by
  funext i
  have h : ¬ ∃ j, data j = address i := by
    rintro ⟨j, hj⟩
    exact hDisjoint i j hj.symm
  simp [loadAtBasis, h]

/-- Wires outside the data view are unchanged. -/
theorem loadAt_other {wireCount a d : Nat} (address : View wireCount a)
    (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d) (state : Reg wireCount)
    (wire : Fin wireCount) (h : ¬ ∃ j, data j = wire) :
    loadAtBasis address data bank state wire = state wire := by
  simp [loadAtBasis, h]

/-- Loading a fixed bank through the same disjoint views twice is the identity. -/
theorem loadAt_involutive {wireCount a d : Nat} (address : View wireCount a)
    (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d)
    (hDisjoint : DisjointViews address data) :
    Function.Involutive (loadAtBasis address data bank) := by
  intro state
  funext wire
  by_cases h : ∃ j, data j = wire
  · obtain ⟨j, rfl⟩ := h
    rw [loadAt_data]
    unfold ReadOnlyQRAM.loadBasis
    simp only [loadAt_address address data bank hDisjoint, Function.comp_apply]
    rw [loadAt_data]
    simp [ReadOnlyQRAM.loadBasis]
  · rw [loadAt_other address data bank _ _ h, loadAt_other address data bank _ _ h]

/-- A snapshot supplies data by the actual entry handle and its declared dimensions. -/
abbrev Snapshot := (bank : Resource) →
  Option (ReadOnlyQRAM.Bank bank.type.addressWidth bank.type.dataWidth)

/-- A QRAM read with checked views and resolved memory handle. -/
structure ResolvedRead (wireCount : Nat) where
  bank : Resource
  address : View wireCount bank.type.addressWidth
  data : View wireCount bank.type.dataWidth
  disjoint : DisjointViews address data

/-- Check the views a caller forwarded, then select the real entry bank. -/
def ResolvedRead.create (wireCount : Nat) (bank : Resource) (address data : List Nat) :
    Except String (ResolvedRead wireCount) := do
  let a ← View.ofWires wireCount bank.type.addressWidth address
  let d ← View.ofWires wireCount bank.type.dataWidth data
  if h : ∀ i j, a i ≠ d j then return ⟨bank, a, d, h⟩
  else throw "QRAM address and data views overlap"

/-- The full quantum denotation of a resolved read, when its snapshot is supplied. -/
noncomputable def ResolvedRead.matrix {wireCount : Nat} (read : ResolvedRead wireCount)
    (snapshot : Snapshot) : Except String (Matrix (Reg wireCount) (Reg wireCount) ℂ) :=
  match snapshot read.bank with
  | none => .error s!"Missing QRAM snapshot for {read.bank.name}"
  | some bank => .ok (permMatrix (loadAtBasis read.address read.data bank))

/-- Execute the semantic lowering of a resolved QRAM instruction. -/
noncomputable def ResolvedInstruction.loadMatrix (instruction : ResolvedInstruction)
    (wireCount : Nat) (snapshot : Snapshot) :
    Except String (Matrix (Reg wireCount) (Reg wireCount) ℂ) := do
  match instruction with
  | .load bank address data =>
    let read ← ResolvedRead.create wireCount bank address data
    read.matrix snapshot
  | _ => throw "Expected a resolved QRAM read"

/-- On a basis state, the matrix read uses the snapshot selected by the forwarded handle. -/
theorem ResolvedRead.matrix_ket {wireCount : Nat} (read : ResolvedRead wireCount)
    (snapshot : Snapshot) (bank : ReadOnlyQRAM.Bank read.bank.type.addressWidth
      read.bank.type.dataWidth) (h : snapshot read.bank = some bank) (state : Reg wireCount) :
    (read.matrix snapshot).map (fun matrix => ApplyGate matrix (Ket state)) =
      .ok (Ket (loadAtBasis read.address read.data bank state)) := by
  simp only [ResolvedRead.matrix, h, Except.map]
  rw [applyGate_permMatrix_ket (loadAt_involutive _ _ bank read.disjoint)]

/-- The denotation on the entry wires is unitary for any supplied fixed bank. -/
theorem ResolvedRead.matrix_unitary {wireCount : Nat} (read : ResolvedRead wireCount)
    (snapshot : Snapshot) (matrix : Matrix (Reg wireCount) (Reg wireCount) ℂ)
    (h : read.matrix snapshot = .ok matrix) : matrix ∈ Matrix.unitaryGroup (Reg wireCount) ℂ := by
  unfold ResolvedRead.matrix at h
  split at h
  · contradiction
  · rename_i bank _
    cases h
    exact permMatrix_unitary (loadAt_involutive _ _ bank read.disjoint)

/-- The resolved read cancels on arbitrary superpositions with the same snapshot. -/
theorem ResolvedRead.matrix_mul_self {wireCount : Nat} (read : ResolvedRead wireCount)
    (snapshot : Snapshot) (matrix : Matrix (Reg wireCount) (Reg wireCount) ℂ)
    (h : read.matrix snapshot = .ok matrix) : matrix * matrix = 1 := by
  unfold ResolvedRead.matrix at h
  split at h
  · contradiction
  · rename_i bank _
    cases h
    exact permMatrix_mul_self (loadAt_involutive _ _ bank read.disjoint)

end OracqVerify.RIR
