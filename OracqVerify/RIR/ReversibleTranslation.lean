module

public import OracqVerify.RIR.ReversibleFootprint

/-! Commutation of reversible basis actions with bitwise XOR translations. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

namespace BasisWord

def xorWord {n : Nat} (state mask : BasisWord n) : BasisWord n :=
  Vector.ofFn fun wire => state.readBit wire ^^ mask.readBit wire

@[simp] theorem xorWord_bit {n : Nat} (state mask : BasisWord n) (wire : Fin n) :
    (xorWord state mask).readBit wire = (state.readBit wire ^^ mask.readBit wire) := by
  simp [xorWord, readBit]

@[simp] theorem ofFn_readBit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (readBit (Vector.ofFn f) i) = f i := by
  simp [readBit]

theorem eq_of_bits {n : Nat} {x y : BasisWord n}
    (equal : ∀ wire, x.readBit wire = y.readBit wire) : x = y :=
  (basis n).injective (funext equal)

def ZeroOn {n : Nat} (mask : BasisWord n) (wires : Finset (Fin n)) : Prop :=
  ∀ wire ∈ wires, mask.readBit wire = false

theorem xorWord_of_zero {n : Nat} (state mask : BasisWord n)
    (zero : ∀ wire, mask.readBit wire = false) : xorWord state mask = state := by
  apply eq_of_bits
  intro wire
  rw [xorWord_bit, zero wire]
  cases state.readBit wire <;> rfl

def CommutesWithXor {n : Nat} (wires : Finset (Fin n))
    (run : BasisWord n → BasisWord n) : Prop :=
  ∀ state mask, ZeroOn mask wires → run (xorWord state mask) = xorWord (run state) mask

theorem CommutesWithXor.inverse {n : Nat} {run : BasisWord n ≃ BasisWord n}
    {wires : Finset (Fin n)} (commutes : CommutesWithXor wires run) :
    CommutesWithXor wires run.symm := by
  intro state mask zero
  apply run.injective
  rw [Equiv.apply_symm_apply, commutes _ _ zero, Equiv.apply_symm_apply]

open Qatlib.Foundations.PureStateMath

theorem readView_xorWord {n k : Nat} (view : View n k) (state mask : BasisWord n) :
    readView view (xorWord state mask) = xorWord (readView view state) (readView view mask) := by
  apply eq_of_bits
  intro wire
  simp only [readView_bit, xorWord_bit]

theorem readView_xorWord_of_zero {n k : Nat} (view : View n k) (state mask : BasisWord n)
    (zero : ZeroOn mask (viewWires view)) : readView view (xorWord state mask) = readView view state := by
  rw [readView_xorWord]
  exact xorWord_of_zero _ _ fun i => (readView_bit _ _ _).trans
    (zero _ ((mem_viewWires view _).mpr ⟨i, rfl⟩))

theorem writeView_xorWord {n k : Nat} (view : View n k) (word : BasisWord k)
    (state mask : BasisWord n) :
    writeView view (xorWord word (readView view mask)) (xorWord state mask) =
      xorWord (writeView view word state) mask := by
  apply eq_of_bits
  intro wire
  by_cases used : ∃ i, view i = wire
  · obtain ⟨i, rfl⟩ := used
    simp only [writeView_bit, xorWord_bit, readView_bit]
  · have other : ∀ i, view i ≠ wire := fun i eq => used ⟨i, eq⟩
    simp only [writeView_other _ _ _ _ other, xorWord_bit]

theorem place_commutes {n k : Nat} (view : View n k) (run : BasisWord k ≃ BasisWord k)
    {wires : Finset (Fin k)} (commutes : CommutesWithXor wires run) :
    CommutesWithXor (wires.map view) (place view run) := by
  intro state mask zero
  have localZero : ZeroOn (readView view mask) wires := fun i onWire =>
    (readView_bit _ _ _).trans (zero _ (Finset.mem_map.mpr ⟨i, onWire, rfl⟩))
  change writeView view (run (readView view (xorWord state mask))) (xorWord state mask) =
    xorWord (writeView view (run (readView view state)) state) mask
  rw [readView_xorWord, commutes _ _ localZero, writeView_xorWord]

theorem place_commutes_outside {n k : Nat} (view : View n k) (run : BasisWord k ≃ BasisWord k) :
    CommutesWithXor (viewWires view) (place view run) := by
  apply place_commutes
  intro state mask zero
  rw [xorWord_of_zero _ mask (fun i => zero i (Finset.mem_univ _)),
    xorWord_of_zero _ mask (fun i => zero i (Finset.mem_univ _))]

private theorem neg_xor (a b : Bool) : (!(a ^^ b)) = ((!a) ^^ b) := by
  cases a <;> cases b <;> rfl

theorem flip_commutes {n : Nat} (wire : Fin n) : CommutesWithXor ∅ (flip wire) := by
  unfold flip
  show CommutesWithXor ((∅ : Finset (Fin 1)).map (oneWire wire)) _
  apply place_commutes
  intro state mask _
  apply eq_of_bits
  intro i
  change readBit (Vector.ofFn fun j => !(xorWord state mask).readBit j) i =
    (xorWord (Vector.ofFn fun j => !state.readBit j) mask).readBit i
  simp only [ofFn_readBit, xorWord_bit]
  exact neg_xor (state.readBit i) (mask.readBit i)

private theorem xor_swap (x y z : Bool) : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem load_commutes {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (apart : DisjointViews address data) :
    CommutesWithXor (viewWires address) (load address data bank apart) := by
  intro state mask zero
  have addressEq : (xorWord state mask).readBit ∘ address = state.readBit ∘ address := by
    funext i
    have off := zero _ ((mem_viewWires address _).mpr ⟨i, rfl⟩)
    change (xorWord state mask).readBit (address i) = state.readBit (address i)
    rw [xorWord_bit, off]
    cases state.readBit (address i) <;> rfl
  let update (input : BasisWord n) := Vector.ofFn fun j =>
    input.readBit (data j) ^^ bank (input.readBit ∘ address) j
  have dataEq : update (xorWord state mask) = xorWord (update state) (readView data mask) := by
    apply eq_of_bits
    intro j
    simp only [update, xorWord_bit, readView_bit, ofFn_readBit]
    rw [addressEq, xor_swap]
  change writeView data (update (xorWord state mask)) (xorWord state mask) =
    xorWord (writeView data (update state) state) mask
  rw [dataEq, writeView_xorWord]

end BasisWord
end OracqVerify.RIR
