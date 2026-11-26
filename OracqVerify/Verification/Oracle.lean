module

public import OracqVerify.Generators.DeutschJozsa
public import OracqVerify.RIR.QRAM
public import Mathlib.Data.List.FinRange

/-! Boolean oracle specifications and executable promise checks for Deutsch–Jozsa. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.DeutschJozsa

open Lean OracqVerify.RIR
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

inductive Promise where
  | constant | balanced
  deriving Repr, DecidableEq

@[expose] def Promise.Holds {width : Nat} (promise : Promise) (f : Reg width → Bool) : Prop :=
  match promise with
  | .constant => DJConstant f
  | .balanced => DJBalanced f

/-- Address integers use the Oracq convention with wire zero least significant. -/
abbrev addressIndex := orderedBitsIndex

/-- The answer-independent highest address bit has weight two to the previous width. -/
theorem addressIndex_succ (width : Nat) (address : Reg (width + 1)) :
    (addressIndex (width + 1) address).val =
      (if address (Fin.last width) then 2 ^ width else 0) +
        (addressIndex width (fun i => address i.castSucc)).val :=
  orderedBitsIndex_succ width address

/-- A full dense snapshot of one-bit QRAM words. -/
structure DenseTable (width : Nat) where
  cells : Array Bool
  size_eq : cells.size = 2 ^ width

def DenseTable.atIndex {width : Nat} (table : DenseTable width)
    (index : Fin (2 ^ width)) : Bool :=
  table.cells[index.cast table.size_eq.symm]

def DenseTable.value {width : Nat} (table : DenseTable width) (address : Reg width) : Bool :=
  table.atIndex (addressIndex width address)

def DenseTable.bank {width : Nat} (table : DenseTable width) : ReadOnlyQRAM.Bank width 1 :=
  fun address _ => table.value address

theorem DenseTable.bank_atIndex {width : Nat} (table : DenseTable width) (address : Reg width)
    (bit : Fin 1) : table.bank address bit = table.atIndex (addressIndex width address) := by
  simp only [DenseTable.bank, DenseTable.value]

/-- Read the named bank from a dense Oracq-style address-ordered JSON word map. -/
def DenseTable.decode (width : Nat) (bank : String) (snapshot : Json) :
    Except String (DenseTable width) := do
  let words ← snapshot.getObjValAs? (Array Nat) bank
  if h : words.size = 2 ^ width then
    unless words.all (fun word => word ≤ 1) do
      throw s!"Bank {bank} contains a word outside the one-bit data range"
    let result := words.map (· == 1)
    return ⟨result, by simpa [result] using h⟩
  else throw s!"Bank {bank} must supply exactly 2^{width} words"

private theorem DenseTable.count_eq {width : Nat} (table : DenseTable width) :
    (Finset.univ.filter (fun x : Reg width => table.value x)).card =
      (List.finRange (2 ^ width)).countP table.atIndex := by
  let addresses := (List.finRange (2 ^ width)).map (addressIndex width).symm
  have hn : addresses.Nodup :=
    (List.nodup_finRange _).map (addressIndex width).symm.injective
  have hfull : addresses.toFinset = (Finset.univ : Finset (Reg width)) := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨addressIndex width x, List.mem_finRange _,
        (addressIndex width).symm_apply_apply x⟩
  rw [← hfull, hn.card_eq_countP, List.countP_map]
  simp [DenseTable.value, Function.comp_def]

/-- Classify a table by its actual contents, rejecting all non-promised functions. -/
def DenseTable.checkPromise {width : Nat} (table : DenseTable width) :
    Except String {kind : Promise // kind.Holds table.value} := do
  if h : ∀ index : Fin (2 ^ width), table.atIndex index = false then
    return ⟨.constant, false, fun x => h (addressIndex width x)⟩
  if h : ∀ index : Fin (2 ^ width), table.atIndex index = true then
    return ⟨.constant, true, fun x => h (addressIndex width x)⟩
  if h : 2 * (List.finRange (2 ^ width)).countP table.atIndex = 2 ^ width then
    return ⟨.balanced, (djBalanced_iff_counts table.value).2 (by rw [table.count_eq]; exact h)⟩
  throw "QRAM oracle is neither constant nor balanced"

private def flipBit {width : Nat} (i : Fin width) : Reg width ≃ Reg width :=
  let flip (x : Reg width) := Function.update x i (!(x i))
  have h : Function.Involutive flip := by
    intro x
    funext j
    by_cases h : j = i
    · subst j
      simp [flip]
    · simp [flip, Function.update_of_ne h]
  h.toPerm

/-- Projection onto any address coordinate is balanced, without enumerating addresses. -/
theorem inputBit_balanced {width : Nat} (i : Fin width) : DJBalanced (fun x : Reg width => x i) := by
  let f : Reg width → Bool := fun x => x i
  have h := (flipBit i).sum_comp (djSign f)
  have hneg (x : Reg width) : djSign f (flipBit i x) = -djSign f x := by
    have hflip : flipBit i x i = !(x i) := by
      change Function.update x i (!(x i)) i = _
      simp
    cases hx : x i <;> simp [djSign, f, hflip, hx]
  simp_rw [hneg, Finset.sum_neg_distrib] at h
  change (∑ x, djSign f x) = 0
  linear_combination -(1 / 2 : ℂ) * h

/-- Reindex a one-bit QRAM read onto the same input/answer basis as the DJ theorem. -/
noncomputable def tableMatrix {width : Nat} (table : DenseTable width) :
    Matrix (Reg width × Bool) (Reg width × Bool) ℂ :=
  let e := Equiv.prodCongr (Equiv.refl (Reg width)) (Equiv.funUnique (Fin 1) Bool)
  Matrix.reindex e e (ReadOnlyQRAM.loadMatrix table.bank)

/-- The resolved full-address, one-bit read implements the standard XOR oracle. -/
theorem tableMatrix_spec {width : Nat} (table : DenseTable width) :
    tableMatrix table = BitOracleOn table.value := by
  ext x y
  let e := Equiv.prodCongr (Equiv.refl (Reg width)) (Equiv.funUnique (Fin 1) Bool)
  change permMatrix (ReadOnlyQRAM.loadBasis table.bank) (e.symm x) (e.symm y) =
    permMatrix (BitFlip table.value) x y
  have h : e (ReadOnlyQRAM.loadBasis table.bank (e.symm y)) = BitFlip table.value y := rfl
  simp only [permMatrix, Matrix.of_apply, ← h, e.symm_apply_eq]

theorem zeroOracle (width : Nat) :
    BitOracleOn (fun _ : Reg width => false) = 1 := by
  ext x y
  simp [BitOracleOn, BitFlip, permMatrix, Matrix.one_apply]

theorem oneOracle (width : Nat) :
    BitOracleOn (fun _ : Reg width => true) = TensorGate 1 PauliX := by
  funext x y
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  simp only [BitOracleOn, BitFlip, Bool.xor_true, permMatrix, Matrix.of_apply,
    tensorGate_apply, Matrix.one_apply, PauliX, Prod.mk.injEq]
  by_cases h : a = b <;> simp [h]

end OracqVerify.Verification.DeutschJozsa
