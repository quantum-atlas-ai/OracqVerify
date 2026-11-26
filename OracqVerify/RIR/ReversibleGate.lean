module

public import OracqVerify.RIR.ReversibleTranslation

/-! Lower the reversible RIR fragment to basis permutations with checked guard footprints. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

structure ReversibleGate (n : Nat) where
  action : BasisWord n ≃ BasisWord n
  writes : Finset (Fin n)
  support : Finset (Fin n)
  writes_supported : writes ⊆ support
  same : ∀ state wire, wire ∉ writes → (action state).readBit wire = state.readBit wire
  forward : BasisWord.DependsOn support action
  backward : BasisWord.DependsOn support action.symm
  xorDependencies : Finset (Fin n)
  commutes : BasisWord.CommutesWithXor xorDependencies action

namespace ReversibleGate

noncomputable def matrix {n : Nat} (gate : ReversibleGate n) : WireMatrix n :=
  BasisWord.matrix gate.action

theorem inverse_same {n : Nat} (gate : ReversibleGate n) (state : BasisWord n)
    (wire : Fin n) (apart : wire ∉ gate.writes) :
    (gate.action.symm state).readBit wire = state.readBit wire := by
  have equal := gate.same (gate.action.symm state) wire apart
  rw [Equiv.apply_symm_apply] at equal
  exact equal.symm

theorem forward_on {n : Nat} (gate : ReversibleGate n) {wires : Finset (Fin n)}
    (included : gate.support ⊆ wires) : BasisWord.DependsOn wires gate.action :=
  gate.forward.mono (fun state wire apart => gate.same state wire fun h =>
    apart (gate.writes_supported h)) included

theorem backward_on {n : Nat} (gate : ReversibleGate n) {wires : Finset (Fin n)}
    (included : gate.support ⊆ wires) : BasisWord.DependsOn wires gate.action.symm :=
  gate.backward.mono (fun state wire apart => gate.inverse_same state wire fun h =>
    apart (gate.writes_supported h)) included

def id (n : Nat) : ReversibleGate n where
  action := Equiv.refl _
  writes := ∅
  support := ∅
  writes_supported := Finset.Subset.rfl
  same _ _ _ := rfl
  forward _ _ agree := agree
  backward _ _ agree := agree
  xorDependencies := ∅
  commutes _ _ _ := rfl

def thenRun {n : Nat} (first second : ReversibleGate n) : ReversibleGate n where
  action := first.action.trans second.action
  writes := first.writes ∪ second.writes
  support := first.support ∪ second.support
  writes_supported := Finset.union_subset_union first.writes_supported second.writes_supported
  same state wire apart := by
    rw [Finset.mem_union, not_or] at apart
    exact (second.same _ wire apart.2).trans (first.same _ wire apart.1)
  forward x y agree :=
    second.forward_on Finset.subset_union_right _ _
      (first.forward_on Finset.subset_union_left x y agree)
  backward x y agree :=
    first.backward_on Finset.subset_union_left _ _
      (second.backward_on Finset.subset_union_right x y agree)
  xorDependencies := first.xorDependencies ∪ second.xorDependencies
  commutes state mask zero := by
    change second.action (first.action (BasisWord.xorWord state mask)) = _
    rw [first.commutes _ _ (fun i hi => zero i (Finset.mem_union_left _ hi)),
      second.commutes _ _ (fun i hi => zero i (Finset.mem_union_right _ hi))]
    rfl

def reversed {n : Nat} (gate : ReversibleGate n) : ReversibleGate n :=
  ⟨gate.action.symm, gate.writes, gate.support, gate.writes_supported,
    gate.inverse_same, gate.backward, gate.forward, gate.xorDependencies, gate.commutes.inverse⟩

theorem placedView_depends {n k : Nat} (view : View n k) {support : Finset (Fin k)}
    {run : BasisWord k → BasisWord k} (uses : BasisWord.DependsOn support run) :
    BasisWord.DependsOn (support.map view)
      (fun state => BasisWord.writeView view (run (BasisWord.readView view state)) state) := by
  intro x y agree wire member
  obtain ⟨i, used, rfl⟩ := Finset.mem_map.mp member
  have inputs : BasisWord.AgreeOn support (BasisWord.readView view x)
      (BasisWord.readView view y) := by
    intro j hj
    simpa only [BasisWord.readView_bit] using agree _ (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
  simpa only [BasisWord.writeView_bit] using uses _ _ inputs i used

def placed {n k : Nat} (view : View n k) (gate : ReversibleGate k) :
    ReversibleGate n where
  action := BasisWord.place view gate.action
  writes := gate.writes.map view
  support := gate.support.map view
  writes_supported := Finset.map_subset_map.mpr gate.writes_supported
  same state wire apart := by
    by_cases located : ∃ i, view i = wire
    · obtain ⟨i, rfl⟩ := located
      change (BasisWord.writeView view (gate.action (BasisWord.readView view state)) state).readBit
        (view i) = _
      rw [BasisWord.writeView_bit, gate.same _ i (by simpa using apart), BasisWord.readView_bit]
    · exact BasisWord.place_preserves _ _ _ _ (fun i equal => located ⟨i, equal⟩)
  forward := placedView_depends view gate.forward
  backward := placedView_depends view gate.backward
  xorDependencies := gate.xorDependencies.map view
  commutes := BasisWord.place_commutes view gate.action gate.commutes

def flip {n : Nat} (wire : Fin n) : ReversibleGate n :=
  ⟨BasisWord.flip wire, BasisWord.viewWires (BasisWord.oneWire wire),
    BasisWord.viewWires (BasisWord.oneWire wire), Finset.Subset.rfl,
    fun state pos apart => BasisWord.place_preserves _ _ state pos
      (fun i eq => apart ((BasisWord.mem_viewWires _ pos).mpr ⟨i, eq⟩)),
    BasisWord.placed_depends _ _, BasisWord.placed_depends _ _, ∅, BasisWord.flip_commutes wire⟩

def add {n k : Nat} (view : View n k) (amount : BitVec k) : ReversibleGate n :=
  ⟨BasisWord.add view amount, BasisWord.viewWires view, BasisWord.viewWires view, Finset.Subset.rfl,
    fun state wire apart => BasisWord.place_preserves view _ state wire
      (fun i eq => apart ((BasisWord.mem_viewWires view wire).mpr ⟨i, eq⟩)),
    BasisWord.placed_depends view _, BasisWord.placed_depends view _,
    BasisWord.viewWires view, BasisWord.place_commutes_outside view _⟩

def load {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (apart : DisjointViews address data) : ReversibleGate n :=
  ⟨BasisWord.load address data bank apart, BasisWord.viewWires data,
    BasisWord.viewWires address ∪ BasisWord.viewWires data, Finset.subset_union_right,
    fun state wire unchanged => BasisWord.writeView_other _ _ state wire
      (fun i eq => unchanged ((BasisWord.mem_viewWires data wire).mpr ⟨i, eq⟩)),
    BasisWord.load_depends address data bank apart, BasisWord.load_depends address data bank apart,
    BasisWord.viewWires address, BasisWord.load_commutes address data bank apart⟩

theorem guard_eq {n k : Nat} (gate : ReversibleGate n) (view : View n k) (value : Nat)
    (apart : ∀ i, view i ∉ gate.writes) (state : BasisWord n) :
    guardEnabled view value (gate.action state).readBit = guardEnabled view value state.readBit := by
  simp only [guardEnabled, gate.same _ _ (apart _)]

def controlled {n k : Nat} (gate : ReversibleGate n) (view : View n k) (value : Nat)
    (apart : ∀ i, view i ∉ gate.writes) : ReversibleGate n := by
  let enabled (state : BasisWord n) := guardEnabled view value state.readBit
  have forward (state : BasisWord n) : enabled (gate.action state) = enabled state :=
    guard_eq gate view value apart state
  have backward (state : BasisWord n) : enabled (gate.action.symm state) = enabled state := by
    rw [← forward (gate.action.symm state), Equiv.apply_symm_apply]
  let action : BasisWord n ≃ BasisWord n :=
    ⟨fun state => if enabled state then gate.action state else state,
      fun state => if enabled state then gate.action.symm state else state,
      by
        intro state
        by_cases on : enabled state = true <;> simp [on, forward],
      by
        intro state
        by_cases on : enabled state = true <;> simp [on, backward]⟩
  let support := gate.support ∪ BasisWord.viewWires view
  have enabled_congr (x y : BasisWord n) (same : BasisWord.AgreeOn support x y) :
      enabled x = enabled y := by
    have bits : x.readBit ∘ view = y.readBit ∘ view := by
      funext i
      exact same _ (Finset.mem_union_right _ ((BasisWord.mem_viewWires view _).mpr ⟨i, rfl⟩))
    exact congrArg (fun data => (List.finRange k).all fun i => data i == value.testBit i.val) bits
  have branch_depends (run : BasisWord n → BasisWord n) (uses : BasisWord.DependsOn support run) :
      BasisWord.DependsOn support (fun state => if enabled state then run state else state) := by
    intro x y same
    dsimp only
    rw [enabled_congr x y same]
    split
    · exact uses x y same
    · exact same
  refine ⟨action, gate.writes, support, gate.writes_supported.trans Finset.subset_union_left, ?_,
    branch_depends gate.action (gate.forward_on Finset.subset_union_left),
    branch_depends gate.action.symm (gate.backward_on Finset.subset_union_left),
    gate.xorDependencies ∪ BasisWord.viewWires view, ?_⟩
  · intro state wire unchanged
    change (if enabled state then gate.action state else state).readBit wire = _
    split
    · exact gate.same state wire unchanged
    · rfl
  · intro state mask zero
    have guardZero : BasisWord.ZeroOn mask (BasisWord.viewWires view) :=
      fun i h => zero i (Finset.mem_union_right _ h)
    have sameGuard : enabled (BasisWord.xorWord state mask) = enabled state := by
      unfold enabled guardEnabled
      have same := BasisWord.readView_xorWord_of_zero view state mask guardZero
      apply congrArg (List.all (List.finRange k))
      funext i
      have bit := congrArg (fun word : BasisWord k => word.readBit i) same
      simp only [BasisWord.readView_bit] at bit
      rw [bit]
    change (if enabled (BasisWord.xorWord state mask) then
        gate.action (BasisWord.xorWord state mask) else BasisWord.xorWord state mask) =
      BasisWord.xorWord (if enabled state then gate.action state else state) mask
    rw [sameGuard]
    split
    · exact gate.commutes _ _ (fun i hi => zero i (Finset.mem_union_left _ hi))
    · rfl

theorem matrix_controlled {n k : Nat} (gate : ReversibleGate n) (view : View n k) (value : Nat)
    (apart : ∀ i, view i ∉ gate.writes) :
    (gate.controlled view value apart).matrix =
      controlledMatrix (matchesGuard view value) gate.matrix := by
  classical
  ext row col
  let p := BasisWord.perm gate.action
  have branch : BasisWord.perm (gate.controlled view value apart).action col =
      if matchesGuard view value col then p col else col := by
    have enabled : guardEnabled view value ((BasisWord.basis n).symm col).readBit =
        guardEnabled view value col := by
      simp only [show ((BasisWord.basis n).symm col).readBit = col from
        (BasisWord.basis n).apply_symm_apply col]
    change ((BasisWord.basis n)
      (if guardEnabled view value ((BasisWord.basis n).symm col).readBit then
        gate.action ((BasisWord.basis n).symm col)
      else (BasisWord.basis n).symm col)) = _
    rw [enabled]
    by_cases h : matchesGuard view value col
    · rw [ite_eq_left ((guardEnabled_spec view value col).mpr h), ite_eq_left h]
      rfl
    · rw [ite_eq_right (fun trueGuard => h ((guardEnabled_spec view value col).mp trueGuard)),
        ite_eq_right h, Equiv.apply_symm_apply]
  have retained (i : Fin k) : p col (view i) = col (view i) := by
    change (gate.action ((BasisWord.basis n).symm col)).readBit (view i) = col (view i)
    rw [gate.same _ _ (apart i), BasisWord.basis_symm_bit]
  have sameGuard : matchesGuard view value (p col) ↔ matchesGuard view value col := by
    simp only [matchesGuard, retained]
  change (if row = BasisWord.perm (gate.controlled view value apart).action col then
    (1 : ℂ) else 0) = controlledMatrix (matchesGuard view value) gate.matrix row col
  rw [branch]
  by_cases c : matchesGuard view value col
  · rw [ite_eq_left c]
    by_cases r : matchesGuard view value row
    · simp [controlledMatrix, r, c, matrix, BasisWord.matrix, permMatrix, p]
    · have outside : row ≠ p col := fun eq => r (eq ▸ sameGuard.mpr c)
      have offDiag : row ≠ col := fun eq => r (eq ▸ c)
      simp [controlledMatrix, r, c, outside, offDiag]
  · rw [ite_eq_right c]
    simp [controlledMatrix, c, Matrix.one_apply]

def flips {n : Nat} : List (Fin n) → ReversibleGate n
  | [] => id n
  | wire :: rest => (flip wire).thenRun (flips rest)

theorem matrix_flips {n : Nat} (wires : List (Fin n)) :
    (flips wires).matrix = wordMatrix (wires.map fun wire => atWire wire PauliX) := by
  induction wires with
  | nil => exact BasisWord.matrix_refl _
  | cons wire rest ih =>
    change BasisWord.matrix ((flip wire).action.trans (flips rest).action) =
      wordMatrix (rest.map fun wire => atWire wire PauliX) * atWire wire PauliX
    rw [BasisWord.matrix_trans, ← ih]
    exact congrArg (fun target => (flips rest).matrix * target) (BasisWord.matrix_flip wire)

end ReversibleGate

abbrev ReversibleOracle (n : Nat) := CallSite → Except String (ReversibleGate n)

/-- Lower the reversible subset, checking the footprint before applying a control. -/
def ResolvedInstruction.compileReversible (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) : ResolvedInstruction → Except String (ReversibleGate n)
  | .unary .x wires => do
    let view ← View.ofWires n wires.length wires
    return ReversibleGate.flips ((List.finRange wires.length).map view)
  | .xor source target => do
    let address ← View.ofWires n source.length source
    let data ← View.ofWires n source.length target
    if apart : ∀ i j, address i ≠ data j then
      return ReversibleGate.load address data id apart
    else throw "XOR views overlap"
  | .addConst wires amount => do
    let view ← View.ofWires n wires.length wires
    return ReversibleGate.add view (BitVec.ofNat wires.length amount)
  | .load bank address data => do
    let read ← ResolvedRead.create n bank address data
    match snapshot read.bank with
    | none => throw s!"Missing QRAM snapshot for {read.bank.name}"
    | some contents => return ReversibleGate.load read.address read.data contents read.disjoint
  | .query name arguments banks => calls ⟨name, arguments, banks⟩
  | .adjoint body => (compileReversible n snapshot calls body).map ReversibleGate.reversed
  | .controlled guard body => do
    let view ← View.ofWires n guard.wires.length guard.wires
    let compiled ← compileReversible n snapshot calls body
    if apart : ∀ i, view i ∉ compiled.writes then
      return compiled.controlled view guard.value apart
    else throw "Controlled reversible gate can write a guard wire"
  | _ => .error "Expected a reversible basis gate"

/-- Resolved controls surround the adjoint; an adjoint already present is cancelled. -/
def ResolvedInstruction.reversibleAdjoint : ResolvedInstruction → ResolvedInstruction
  | .controlled guard body => .controlled guard body.reversibleAdjoint
  | .adjoint body => body
  | atom => .adjoint atom

theorem ResolvedInstruction.compileReversible_adjoint (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (step : ResolvedInstruction) :
    step.reversibleAdjoint.compileReversible n snapshot calls =
      (step.compileReversible n snapshot calls).map ReversibleGate.reversed := by
  induction step with
  | controlled guard body ih =>
    simp only [reversibleAdjoint, compileReversible, ih, Bind.bind, Except.bind]
    split
    · rfl
    · rename_i view _
      cases compiled : body.compileReversible n snapshot calls with
      | error => rfl
      | ok lower =>
        by_cases apart : ∀ i, view i ∉ lower.writes
        · have apart' : ∀ i, view i ∉ lower.reversed.writes := apart
          simp only [Except.map, dite_eq_left apart, dite_eq_left apart', Pure.pure, Except.pure]
          rfl
        · have apart' : ¬∀ i, view i ∉ lower.reversed.writes := apart
          simp only [Except.map, dite_eq_right apart, dite_eq_right apart']
          rfl
  | adjoint body =>
    simp only [reversibleAdjoint, compileReversible]
    cases body.compileReversible n snapshot calls <;> rfl
  | unary kind wires => cases kind <;> rfl
  | gphase _ | xor _ _ | addConst _ _ | load _ _ _ | query _ _ _ => rfl

theorem ResolvedInstruction.compileReversible_sound (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (oracle : Oracle n)
    (sound : ∀ site gate, calls site = .ok gate → oracle site = .ok gate.matrix)
    (step : ResolvedInstruction) (gate : ReversibleGate n)
    (compiled : step.compileReversible n snapshot calls = .ok gate) :
    step.matrixWith n snapshot oracle = .ok gate.matrix := by
  induction step generalizing gate with
  | unary kind wires =>
    cases kind <;> try contradiction
    simp only [compileReversible, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i view decoded
      cases compiled
      simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix, decoded,
        ReversibleGate.matrix_flips, List.map_map, Function.comp_def, unaryMatrix,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | xor source target =>
    simp only [compileReversible, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i address ha
      split at compiled
      · contradiction
      · rename_i data hd
        split at compiled
        · rename_i apart
          cases compiled
          simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix, xorMatrix, ha, hd,
            apart, Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact (BasisWord.matrix_load address data id apart).symm
        · contradiction
  | addConst wires amount =>
    simp only [compileReversible, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i view decoded
      cases compiled
      simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix, addConstMatrix, decoded,
        ReversibleGate.matrix, ReversibleGate.add, BasisWord.matrix_add, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
  | load bank address data =>
    simp only [compileReversible, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i read decoded
      split at compiled
      · contradiction
      · rename_i contents supplied
        cases compiled
        simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix,
          ResolvedInstruction.loadMatrix, ResolvedRead.matrix, decoded, supplied,
          ReversibleGate.matrix, ReversibleGate.load, BasisWord.matrix_load,
          Bind.bind, Except.bind]
  | query name arguments banks => exact sound ⟨name, arguments, banks⟩ _ compiled
  | adjoint body ih =>
    simp only [compileReversible, Except.map] at compiled
    split at compiled
    · contradiction
    · rename_i inner decoded
      cases compiled
      simp [ResolvedInstruction.matrixWith, ih _ decoded, ReversibleGate.matrix,
        ReversibleGate.reversed, BasisWord.matrix_symm, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | controlled guard body ih =>
    simp only [compileReversible, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i view decoded
      split at compiled
      · contradiction
      · rename_i inner bodyOk
        split at compiled
        · cases compiled
          simp [ResolvedInstruction.matrixWith, decoded, ih _ bodyOk,
            ReversibleGate.matrix_controlled, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · contradiction
  | gphase _ => contradiction

end OracqVerify.RIR
