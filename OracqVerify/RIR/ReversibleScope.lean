module

public import OracqVerify.RIR.ReversibleWord
public import OracqVerify.RIR.ScopedLink

/-! Certify a scoped reversible word by checking the reachable zero-workspace frame. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath

namespace BasisWord

def enter {p : Nat} (l : Nat) (state : BasisWord p) : BasisWord (p + l) :=
  state ++ Vector.replicate l false

def exit (p l : Nat) (state : BasisWord (p + l)) : BasisWord p :=
  Vector.ofFn fun i => state.readBit (Fin.castAdd l i)

@[simp] theorem exit_enter {p l : Nat} (state : BasisWord p) : exit p l (enter l state) = state := by
  ext i hi
  simp [enter, exit, readBit, Vector.getElem_append_left]

theorem basis_enter {p l : Nat} (state : BasisWord p) :
    basis (p + l) (enter l state) = appendZero p l (basis p state) := by
  funext wire
  change (enter l state).readBit wire = appendZero p l state.readBit wire
  refine Fin.addCases ?_ ?_ wire
  · intro i
    rw [appendZero_public]
    exact Vector.getElem_append_left i.isLt
  · intro i
    rw [appendZero_local]
    simp [enter, readBit, Vector.getElem_append_right]

private theorem enter_exit_zero {p : Nat} (state : BasisWord (p + 0)) :
    enter 0 (exit p 0 state) = state := by
  apply (basis (p + 0)).injective
  funext wire
  rw [basis_enter]
  have eq : wire = Fin.castAdd 0 (⟨wire.val, wire.isLt⟩ : Fin p) := rfl
  rw [eq, appendZero_public]
  change (exit p 0 state).readBit ⟨wire.val, wire.isLt⟩ = state.readBit _
  simp [exit, readBit]

def indexed (n : Nat) : Fin (2 ^ n) ≃ BasisWord n :=
  (orderedBitsIndex n).symm.trans (basis n).symm

def cleanOn (p l : Nat) (action : BasisWord (p + l) ≃ BasisWord (p + l))
    (state : BasisWord p) : Bool :=
  let forward := action (enter l state)
  decide (enter l (exit p l forward) = forward)

/-- Check the zero frame on the public basis. Reversibility and finiteness
imply closure under the inverse. The identity frame requires no enumeration. -/
def checkExit (p l : Nat) (action : BasisWord (p + l) ≃ BasisWord (p + l)) : Bool :=
  if l = 0 then true
  else (List.finRange (2 ^ p)).all fun i => cleanOn p l action (indexed p i)

def CleanFrame {p l : Nat} (action : BasisWord (p + l) ≃ BasisWord (p + l)) : Prop :=
  ∀ state, enter l (exit p l (action (enter l state))) = action (enter l state)

theorem checkExit_sound {p l : Nat} {action : BasisWord (p + l) ≃ BasisWord (p + l)}
    (checked : checkExit p l action = true) : CleanFrame action := by
  intro input
  by_cases noLocals : l = 0
  · subst l
    exact enter_exit_zero _
  · have tests := checked
    simp only [checkExit, ite_eq_right noLocals, List.all_eq_true] at tests
    let index := (indexed p).symm input
    have done := tests index (List.mem_finRange index)
    have equal : indexed p index = input := (indexed p).apply_symm_apply input
    rw [equal] at done
    exact of_decide_eq_true done

theorem CleanFrame.symm {p l : Nat} {action : BasisWord (p + l) ≃ BasisWord (p + l)}
    (forward : CleanFrame (p := p) (l := l) action) : CleanFrame (p := p) (l := l) action.symm := by
  intro state
  let _ : Fintype (BasisWord p) := Fintype.ofEquiv (Reg p) (basis p).symm
  let publicAction : BasisWord p → BasisWord p := fun input => exit p l (action (enter l input))
  have injective : Function.Injective publicAction := by
    intro a b equal
    have encoded := congrArg (enter l) equal
    change enter l (exit p l (action (enter l a))) = enter l (exit p l (action (enter l b))) at encoded
    rw [forward a, forward b] at encoded
    have same := congrArg (exit p l) (action.injective encoded)
    simpa using same
  obtain ⟨prior, reaches⟩ := Finite.surjective_of_injective injective state
  have reachesFrame : action (enter l prior) = enter l state := by
    rw [← reaches]
    exact (forward prior).symm
  rw [← reachesFrame, Equiv.symm_apply_apply, exit_enter]

def restrict {p l : Nat} (action : BasisWord (p + l) ≃ BasisWord (p + l))
    (clean : CleanFrame (p := p) (l := l) action) : BasisWord p ≃ BasisWord p where
  toFun state := exit p l (action (enter l state))
  invFun state := exit p l (action.symm (enter l state))
  left_inv state := by
    change exit p l (action.symm (enter l (exit p l (action (enter l state))))) = _
    rw [clean state, Equiv.symm_apply_apply, exit_enter]
  right_inv state := by
    change exit p l (action (enter l (exit p l (action.symm (enter l state))))) = _
    rw [clean.symm state, Equiv.apply_symm_apply, exit_enter]

theorem restrict_congr {p l : Nat} {a b : BasisWord (p + l) ≃ BasisWord (p + l)}
    (same : a = b) (cleanA : CleanFrame (p := p) (l := l) a)
    (cleanB : CleanFrame (p := p) (l := l) b) :
    restrict a cleanA = restrict b cleanB := by
  cases same
  rfl

theorem restrict_intertwines {p l : Nat} (action : BasisWord (p + l) ≃ BasisWord (p + l))
    (clean : CleanFrame (p := p) (l := l) action) (column : Reg p) :
    perm action (appendZero p l column) =
      appendZero p l (perm (restrict action clean) column) := by
  let input := (basis p).symm column
  have col : basis p input = column := (basis p).apply_symm_apply column
  have embedding : (basis (p + l)).symm (appendZero p l column) = enter l input := by
    apply (basis (p + l)).injective
    rw [Equiv.apply_symm_apply, basis_enter, col]
  change basis (p + l) (action ((basis (p + l)).symm (appendZero p l column))) =
    appendZero p l (basis p (restrict action clean input))
  rw [embedding, ← basis_enter]
  exact congrArg (basis (p + l)) (clean input).symm

theorem restrict_clean (m : ScopedModule) (action : BasisWord m.width ≃ BasisWord m.width)
    (checked : CleanFrame (p := m.publicWires) (l := m.localWires) action) :
    m.Clean (matrix action) := by
  apply (m.clean_iff_zero_off_frame (matrix action)).mpr
  intro row col outside
  simp [matrix, permMatrix, restrict_intertwines action checked, outside]

theorem restrict_matrix (m : ScopedModule) (action : BasisWord m.width ≃ BasisWord m.width)
    (checked : CleanFrame (p := m.publicWires) (l := m.localWires) action) :
    m.publicMatrix (matrix action) = matrix (restrict action checked) := by
  ext row col
  rw [ScopedModule.publicMatrix, ScopedModule.frame, basisFrame_compress]
  simp [matrix, permMatrix, restrict_intertwines action checked,
    (appendZero m.publicWires m.localWires).injective.eq_iff]

theorem enter_bit {p l : Nat} (state : BasisWord p) (wire : Fin p) :
    (enter l state).readBit (Fin.castAdd l wire) = state.readBit wire := by
  exact Vector.getElem_append_left wire.isLt

theorem enter_local_bit {p l : Nat} (state : BasisWord p) (wire : Fin l) :
    (enter l state).readBit (Fin.natAdd p wire) = false := by
  simp [enter, readBit, Vector.getElem_append_right]

@[simp] theorem exit_bit {p l : Nat} (state : BasisWord (p + l)) (wire : Fin p) :
    (exit p l state).readBit wire = state.readBit (Fin.castAdd l wire) := by
  simp [exit, readBit]


theorem enter_xorWord {p l : Nat} (state mask : BasisWord p) :
    enter l (xorWord state mask) = xorWord (enter l state) (enter l mask) := by
  apply eq_of_bits
  intro wire
  refine Fin.addCases ?_ ?_ wire
  · intro i
    simp only [enter_bit, xorWord_bit]
  · intro i
    simp only [xorWord_bit, enter_local_bit]
    rfl

theorem exit_xorWord {p l : Nat} (state mask : BasisWord (p + l)) :
    exit p l (xorWord state mask) = xorWord (exit p l state) (exit p l mask) := by
  apply eq_of_bits
  intro wire
  simp only [exit_bit, xorWord_bit]

theorem cleanFrame_of_fixed {p l : Nat} {action : BasisWord (p + l) ≃ BasisWord (p + l)}
    (fixed : ∀ state (wire : Fin l),
      (action state).readBit (Fin.natAdd p wire) = state.readBit (Fin.natAdd p wire)) :
    CleanFrame (p := p) (l := l) action := by
  intro state
  apply (basis (p + l)).injective
  funext wire
  refine Fin.addCases ?_ ?_ wire
  · intro i
    change (enter l (exit p l (action (enter l state)))).readBit (Fin.castAdd l i) = _
    rw [enter_bit, exit_bit]
    rfl
  · intro i
    change (enter l (exit p l (action (enter l state)))).readBit (Fin.natAdd p i) =
      (action (enter l state)).readBit (Fin.natAdd p i)
    rw [fixed, enter_local_bit, enter_local_bit]

end BasisWord

namespace ReversibleGate

/-- Each scoped result carries its public wire effects into subsequent calls. -/
def restrict {p l : Nat} (gate : ReversibleGate (p + l))
    (clean : BasisWord.CleanFrame (p := p) (l := l) gate.action) : ReversibleGate p where
  action := BasisWord.restrict gate.action clean
  writes := Finset.univ.filter fun wire => Fin.castAdd l wire ∈ gate.writes
  support := Finset.univ.filter fun wire => Fin.castAdd l wire ∈ gate.support
  writes_supported := fun _ h => by simpa using gate.writes_supported (by simpa using h)
  same state wire apart := by
    change (BasisWord.exit p l (gate.action (BasisWord.enter l state))).readBit wire = _
    rw [BasisWord.exit_bit, gate.same _ _ (by simpa using apart), BasisWord.enter_bit]
  forward x y agree wire used := by
    have inputs : BasisWord.AgreeOn gate.support (BasisWord.enter l x) (BasisWord.enter l y) := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j hj
        rw [BasisWord.enter_bit, BasisWord.enter_bit]
        exact agree j (by simpa using hj)
      · intro j _
        rw [BasisWord.enter_local_bit, BasisWord.enter_local_bit]
    have equal := gate.forward _ _ inputs (Fin.castAdd l wire) (by simpa using used)
    simpa only [BasisWord.restrict, Equiv.coe_fn_mk, BasisWord.exit_bit] using equal
  backward x y agree wire used := by
    have inputs : BasisWord.AgreeOn gate.support (BasisWord.enter l x) (BasisWord.enter l y) := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j hj
        rw [BasisWord.enter_bit, BasisWord.enter_bit]
        exact agree j (by simpa using hj)
      · intro j _
        rw [BasisWord.enter_local_bit, BasisWord.enter_local_bit]
    have equal := gate.backward _ _ inputs (Fin.castAdd l wire) (by simpa using used)
    simpa only [BasisWord.restrict, Equiv.symm_mk, Equiv.coe_fn_mk, BasisWord.exit_bit] using equal

  xorDependencies := Finset.univ.filter fun wire => Fin.castAdd l wire ∈ gate.xorDependencies
  commutes state mask zero := by
    have extended : BasisWord.ZeroOn (BasisWord.enter l mask) gate.xorDependencies := by
      intro wire
      refine Fin.addCases ?_ ?_ wire
      · intro i present
        rw [BasisWord.enter_bit]
        exact zero i (by simpa using present)
      · intro i _
        exact BasisWord.enter_local_bit mask i
    change BasisWord.exit p l (gate.action (BasisWord.enter l (BasisWord.xorWord state mask))) =
      BasisWord.xorWord (BasisWord.exit p l (gate.action (BasisWord.enter l state))) mask
    rw [BasisWord.enter_xorWord, gate.commutes _ _ extended, BasisWord.exit_xorWord, BasisWord.exit_enter]

end ReversibleGate

structure ReversibleFrame (m : ScopedModule) (body : ReversibleGate m.width) where
  gate : ReversibleGate m.width
  sameAction : gate.action = body.action
  clean : BasisWord.CleanFrame (p := m.publicWires) (l := m.localWires) gate.action

/-- The lowerer only trusts a setup/uncompute split after checking the entire
word against that decomposition. -/
def certifyReversibleFrame (m : ScopedModule) (snapshot : Snapshot)
    (calls : ReversibleOracle m.width) (steps : List ResolvedInstruction)
    (body : ReversibleGate m.width)
    (compiled : compileReversibleWord m.width snapshot calls steps = .ok body) :
    Option (ReversibleFrame m body) := do
  let mirrored := (steps.zip steps.reverse).takeWhile fun pair =>
    decide (pair.1.reversibleAdjoint = pair.2)
  let size := min mirrored.length (steps.length / 2)
  let setupSteps := steps.take size
  let middle := (steps.drop size).take (steps.length - 2 * size)
  if shape : steps = setupSteps ++ (middle ++ setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint) then
    match setupOk : compileReversibleWord m.width snapshot calls setupSteps with
    | .error _ => none
    | .ok setup =>
      match writeOk : compileReversibleWord m.width snapshot calls middle with
      | .error _ => none
      | .ok rawWrite =>
        let write := narrowReversibleWrites snapshot calls middle rawWrite writeOk fun wire =>
          decide (wire ∈ setup.support ∨ m.publicWires ≤ wire.val)
        if checked : Disjoint setup.support write.writes ∧
            (∀ wire ∈ write.writes, wire.val < m.publicWires) then
          have restored := compileReversibleWord_compute_write_uncompute m.width snapshot calls
            setupSteps middle setup rawWrite write body setupOk writeOk rfl (shape ▸ compiled) checked.1
          let narrowed : ReversibleGate m.width := { body with
            writes := body.writes ∩ write.writes
            writes_supported := Finset.inter_subset_left.trans body.writes_supported
            same := fun state wire absent => by
              by_cases original : wire ∈ body.writes
              · exact restored state wire (fun h => absent (Finset.mem_inter.mpr ⟨original, h⟩))
              · exact body.same state wire original }
          some ⟨narrowed, rfl, BasisWord.cleanFrame_of_fixed fun state wire =>
            restored state (Fin.natAdd m.publicWires wire) (fun h => by
              have inInterface := checked.2 _ h
              change m.publicWires + wire.val < m.publicWires at inInterface
              omega)⟩
        else none
  else none

def ScopedModule.compileReversible (m : ScopedModule) (snapshot : Snapshot)
    (calls : ReversibleOracle m.width) (maxEnumeratedWires : Option Nat) :
    Except String (ReversibleGate m.publicWires) := do
  let some steps := m.body | throw s!"Open scoped slot {m.name}"
  match result : compileReversibleWord m.width snapshot calls steps with
  | .error error => throw error
  | .ok body =>
    if empty : m.localWires = 0 then
      return body.restrict (BasisWord.checkExit_sound (by simp [BasisWord.checkExit, empty]))
    else
      match certifyReversibleFrame m snapshot calls steps body result with
      | some frame => return frame.gate.restrict frame.clean
      | none =>
        if checked : (maxEnumeratedWires.all (m.publicWires ≤ ·) &&
            BasisWord.checkExit m.publicWires m.localWires body.action) = true then
          return body.restrict (BasisWord.checkExit_sound (Bool.and_eq_true_iff.mp checked).2)
        else throw (if maxEnumeratedWires.all (m.publicWires ≤ ·) then s!"Dirty workspace at {m.name}"
          else s!"Workspace enumeration limit exceeded at {m.name}")

theorem ScopedModule.compileReversible_sound (m : ScopedModule) (environment : ScopedEnvironment)
    (snapshot : Snapshot) (calls : ReversibleOracle m.width)
    (sound : ∀ site gate, calls site = .ok gate → environment.atCall m.width snapshot site = .ok gate.matrix)
    (action : ReversibleGate m.publicWires) (maxEnumeratedWires : Option Nat)
    (compiled : m.compileReversible snapshot calls maxEnumeratedWires = .ok action) :
    m.interpret environment snapshot = .ok action.matrix := by
  unfold ScopedModule.compileReversible at compiled
  split at compiled
  · rename_i steps body
    split at compiled
    · contradiction
    · rename_i lowered loweredOk
      have restricted : ∃ clean : BasisWord.CleanFrame
          (p := m.publicWires) (l := m.localWires) lowered.action,
          action.action = BasisWord.restrict lowered.action clean := by
        split at compiled
        · rename_i empty
          cases compiled
          exact ⟨BasisWord.checkExit_sound (by simp [BasisWord.checkExit, empty]), rfl⟩
        · split at compiled
          · rename_i frame _
            cases compiled
            have clean : BasisWord.CleanFrame (p := m.publicWires) (l := m.localWires) lowered.action :=
              frame.sameAction ▸ frame.clean
            refine ⟨clean, ?_⟩
            change BasisWord.restrict frame.gate.action frame.clean = BasisWord.restrict lowered.action clean
            exact BasisWord.restrict_congr frame.sameAction frame.clean clean
          · split at compiled
            · rename_i checked
              cases compiled
              exact ⟨BasisWord.checkExit_sound (Bool.and_eq_true_iff.mp checked).2, rfl⟩
            · contradiction
      obtain ⟨clean, actionEq⟩ := restricted
      have matrices : m.bodyMatrix snapshot (environment.atCall m.width snapshot) =
          .ok lowered.matrix := by
        unfold ScopedModule.bodyMatrix
        rw [body]
        exact compileReversibleWord_sound _ _ _ _ sound _ _ loweredOk
      have cert : m.Certificate snapshot (environment.atCall m.width snapshot) lowered.matrix :=
        ⟨matrices, BasisWord.matrix_unitary _, BasisWord.restrict_clean m _ clean⟩
      rw [cert.interpret]
      simp only [ReversibleGate.matrix, actionEq]
      exact congrArg Except.ok (BasisWord.restrict_matrix m _ clean)
  · contradiction

end OracqVerify.RIR
