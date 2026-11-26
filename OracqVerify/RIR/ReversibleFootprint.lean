module

public import OracqVerify.RIR.ReversibleMatrix

/-! Wire dependencies of a reversible basis action in both directions. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

namespace BasisWord

def AgreeOn {n : Nat} (wires : Finset (Fin n)) (x y : BasisWord n) : Prop :=
  ∀ wire ∈ wires, x.readBit wire = y.readBit wire

def DependsOn {n : Nat} (wires : Finset (Fin n)) (run : BasisWord n → BasisWord n) : Prop :=
  ∀ x y, AgreeOn wires x y → AgreeOn wires (run x) (run y)

theorem DependsOn.mono {n : Nat} {small large : Finset (Fin n)}
    {run : BasisWord n → BasisWord n} (depends : DependsOn small run)
    (fixed : ∀ state wire, wire ∉ small → (run state).readBit wire = state.readBit wire)
    (included : small ⊆ large) : DependsOn large run := by
  intro x y agree wire member
  by_cases onSmall : wire ∈ small
  · exact depends x y (fun i hi => agree i (included hi)) wire onSmall
  · rw [fixed x wire onSmall, fixed y wire onSmall]
    exact agree wire member

def viewWires {n k : Nat} (view : View n k) : Finset (Fin n) :=
  Finset.univ.map view

@[simp] theorem mem_viewWires {n k : Nat} (view : View n k) (wire : Fin n) :
    wire ∈ viewWires view ↔ ∃ index, view index = wire := by
  simp [viewWires]

theorem agree_readView {n k : Nat} {view : View n k} {x y : BasisWord n}
    (agree : AgreeOn (viewWires view) x y) : readView view x = readView view y := by
  apply (basis k).injective
  funext i
  simpa only [Equiv.toFun_as_coe, basis, Equiv.coe_fn_mk, readView_bit] using
    agree (view i) ((mem_viewWires view _).mpr ⟨i, rfl⟩)

theorem placed_depends {n k : Nat} (view : View n k)
    (run : BasisWord k → BasisWord k) :
    DependsOn (viewWires view) (fun state => writeView view (run (readView view state)) state) := by
  intro x y agree wire member
  obtain ⟨i, rfl⟩ := (mem_viewWires view _).mp member
  rw [writeView_bit, writeView_bit, agree_readView agree]

theorem load_depends {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (apart : DisjointViews address data) :
    DependsOn (viewWires address ∪ viewWires data) (load address data bank apart) := by
  intro x y agree wire member
  have sameAddress : x.readBit ∘ address = y.readBit ∘ address := by
    funext i
    exact agree _ (Finset.mem_union_left _ ((mem_viewWires address _).mpr ⟨i, rfl⟩))
  change (writeView data (Vector.ofFn _) x).readBit wire =
    (writeView data (Vector.ofFn _) y).readBit wire
  by_cases inData : wire ∈ viewWires data
  · obtain ⟨i, rfl⟩ := (mem_viewWires data _).mp inData
    rw [writeView_bit, writeView_bit]
    have sameBit := agree (data i) (Finset.mem_union_right _ ((mem_viewWires data _).mpr ⟨i, rfl⟩))
    simp [readBit] at sameBit ⊢
    rw [sameAddress, sameBit]
  · have other : ∀ i, data i ≠ wire := fun i eq => inData ((mem_viewWires data _).mpr ⟨i, eq⟩)
    rw [writeView_other _ _ _ _ other, writeView_other _ _ _ _ other]
    exact agree wire member

end BasisWord
end OracqVerify.RIR
