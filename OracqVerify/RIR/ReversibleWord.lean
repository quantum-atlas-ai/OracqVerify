module

public import OracqVerify.RIR.ReversibleGate

/-! Basis lowering for resolved words and certificates for inverse suffixes. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

namespace ReversibleGate

/-- An output write that leaves the setup's support alone cannot interfere
with its inverse. Every bit outside the output writes is restored. -/
theorem compute_write_uncompute {n : Nat} (setup write : ReversibleGate n)
    (separate : Disjoint setup.support write.writes)
    (state : BasisWord n) (wire : Fin n) (outside : wire ∉ write.writes) :
    (setup.action.symm (write.action (setup.action state))).readBit wire = state.readBit wire := by
  by_cases used : wire ∈ setup.support
  · have label : BasisWord.AgreeOn setup.support (write.action (setup.action state))
        (setup.action state) := fun i hi =>
      write.same _ i (fun updated => Finset.disjoint_left.mp separate hi updated)
    have restored := setup.backward _ _ label wire used
    rwa [Equiv.symm_apply_apply] at restored
  · have fixed : wire ∉ setup.writes := fun h => used (setup.writes_supported h)
    rw [setup.inverse_same _ _ fixed, write.same _ _ outside, setup.same _ _ fixed]

end ReversibleGate

def compileReversibleWord (n : Nat) (snapshot : Snapshot) (calls : ReversibleOracle n) :
    List ResolvedInstruction → Except String (ReversibleGate n)
  | [] => .ok (ReversibleGate.id n)
  | head :: tail => do
    let first ← head.compileReversible n snapshot calls
    let rest ← compileReversibleWord n snapshot calls tail
    return first.thenRun rest

theorem compileReversibleWord_sound (n : Nat) (snapshot : Snapshot)
    (oracle : Oracle n) (calls : ReversibleOracle n)
    (sound : ∀ site gate, calls site = .ok gate → oracle site = .ok gate.matrix)
    (steps : List ResolvedInstruction) (gate : ReversibleGate n)
    (compiled : compileReversibleWord n snapshot calls steps = .ok gate) :
    ((steps.mapM (ResolvedInstruction.matrixWith n snapshot oracle)).map wordMatrix) =
      .ok gate.matrix := by
  induction steps generalizing gate with
  | nil =>
    cases compiled
    exact congrArg Except.ok (BasisWord.matrix_refl _).symm
  | cons step rest ih =>
    simp only [compileReversibleWord, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i first firstOk
      split at compiled
      · contradiction
      · rename_i tail tailOk
        cases compiled
        have headMatrix := step.compileReversible_sound n snapshot calls oracle sound first firstOk
        have tailMatrix := ih _ tailOk
        cases mapped : rest.mapM (ResolvedInstruction.matrixWith n snapshot oracle) with
        | error reason =>
          rw [mapped] at tailMatrix
          cases tailMatrix
        | ok matrices =>
          have equal : wordMatrix matrices = tail.matrix := by
            simpa [mapped, Except.map] using tailMatrix
          simp [List.mapM_cons, headMatrix, mapped, Except.map, wordMatrix, equal,
            ReversibleGate.matrix, ReversibleGate.thenRun, BasisWord.matrix_trans,
            Bind.bind, Except.bind, Pure.pure, Except.pure]


theorem compileReversibleWord_append (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (first second : List ResolvedInstruction) :
    (compileReversibleWord n snapshot calls (first ++ second)).map ReversibleGate.action =
      (do
        let setupSteps ← compileReversibleWord n snapshot calls first
        let suffix ← compileReversibleWord n snapshot calls second
        return setupSteps.action.trans suffix.action) := by
  induction first with
  | nil =>
    rw [List.nil_append, compileReversibleWord]
    cases compileReversibleWord n snapshot calls second <;>
      simp [ReversibleGate.id, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
  | cons head tail ih =>
    simp only [List.cons_append, compileReversibleWord, Bind.bind, Except.bind]
    cases head.compileReversible n snapshot calls with
    | error => rfl
    | ok gate =>
      cases tailOk : compileReversibleWord n snapshot calls tail <;>
        cases secondOk : compileReversibleWord n snapshot calls second <;>
        cases appendOk : compileReversibleWord n snapshot calls (tail ++ second) <;>
        simp_all only [Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure,
          Except.error.injEq, Except.ok.injEq, reduceCtorEq, ReversibleGate.thenRun,
          Equiv.trans_assoc]

theorem compileReversibleWord_inverse (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (steps : List ResolvedInstruction) (gate : ReversibleGate n)
    (compiled : compileReversibleWord n snapshot calls steps = .ok gate) :
    (compileReversibleWord n snapshot calls (steps.reverse.map ResolvedInstruction.reversibleAdjoint)).map
      ReversibleGate.action = .ok gate.action.symm := by
  induction steps generalizing gate with
  | nil => cases compiled; rfl
  | cons head tail ih =>
    simp only [compileReversibleWord, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i first firstOk
      split at compiled
      · contradiction
      · rename_i rest restOk
        cases compiled
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          compileReversibleWord_append]
        have invRest := ih rest restOk
        cases compiledRest : compileReversibleWord n snapshot calls
            (tail.reverse.map ResolvedInstruction.reversibleAdjoint) with
        | error error =>
          rw [compiledRest] at invRest
          cases invRest
        | ok rev =>
          have revEq : rev.action = rest.action.symm := by
            rw [compiledRest] at invRest
            exact Except.ok.inj invRest
          simp only [compileReversibleWord, head.compileReversible_adjoint n snapshot calls,
            firstOk, revEq, ReversibleGate.reversed, ReversibleGate.thenRun, ReversibleGate.id,
            Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          rfl

theorem compileReversibleWord_compute_write_uncompute (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (setupSteps middle : List ResolvedInstruction)
    (setup rawWrite write body : ReversibleGate n)
    (setupOk : compileReversibleWord n snapshot calls setupSteps = .ok setup)
    (writeOk : compileReversibleWord n snapshot calls middle = .ok rawWrite)
    (effect : write.action = rawWrite.action)
    (bodyOk : compileReversibleWord n snapshot calls
      (setupSteps ++ (middle ++ setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint)) =
        .ok body)
    (separate : Disjoint setup.support write.writes)
    (state : BasisWord n) (wire : Fin n) (outside : wire ∉ write.writes) :
    (body.action state).readBit wire = state.readBit wire := by
  have inv := compileReversibleWord_inverse n snapshot calls setupSteps setup setupOk
  cases suffixOk : compileReversibleWord n snapshot calls
      (setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint) with
  | error reason =>
    rw [suffixOk] at inv
    cases inv
  | ok inverse =>
    have invEq : inverse.action = setup.action.symm := by
      rw [suffixOk] at inv
      exact Except.ok.inj inv
    have tail := compileReversibleWord_append n snapshot calls middle
      (setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint)
    rw [writeOk, suffixOk] at tail
    cases tailOk : compileReversibleWord n snapshot calls
        (middle ++ setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint) with
    | error reason =>
      rw [tailOk] at tail
      cases tail
    | ok finish =>
      have finishEq : finish.action = write.action.trans inverse.action := by
        rw [tailOk] at tail
        rw [effect]
        exact Except.ok.inj tail
      have full := compileReversibleWord_append n snapshot calls setupSteps
        (middle ++ setupSteps.reverse.map ResolvedInstruction.reversibleAdjoint)
      have actionEq : body.action = setup.action.trans (write.action.trans setup.action.symm) := by
        rw [bodyOk, setupOk] at full
        simp only [Bind.bind, Except.bind, Except.map] at full
        rw [tailOk] at full
        have replaced : body.action = setup.action.trans finish.action := Except.ok.inj full
        rwa [finishEq, invEq] at replaced
      rw [actionEq]
      exact setup.compute_write_uncompute write separate state wire outside

section

variable {A : Type} [DecidableEq A]

def pairedSources : List A → Bool
  | [] => true
  | first :: rest => if first ∈ rest then pairedSources (rest.erase first) else false
termination_by sources => sources.length
decreasing_by
  exact Nat.lt_succ_of_le List.length_erase_le

private theorem xor_move (x y z : Bool) : xor (xor x y) z = xor (xor x z) y := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem xor_twice (x y : Bool) : xor (xor x y) y = x := by
  cases x <;> cases y <;> rfl

private theorem fold_erase_xor (values : A → Bool) (sources : List A) (source : A)
    (present : source ∈ sources) (start : Bool) :
    sources.foldl (fun bit key => xor bit (values key)) (xor start (values source)) =
      (sources.erase source).foldl (fun bit key => xor bit (values key)) start := by
  induction sources generalizing start with
  | nil => cases present
  | cons head tail ih =>
    by_cases same : head = source
    · subst head
      rw [List.erase_cons_head, List.foldl_cons, xor_twice]
    · have later : source ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      have comparison : ¬ (head == source) := fun equal => same (beq_iff_eq.mp equal)
      rw [List.erase_cons_tail comparison, List.foldl_cons, List.foldl_cons, xor_move,
        ih later]

/-- If every unconditional XOR into one scratch bit has a paired application
from the same unchanged source bit, the circuit restores that scratch bit. -/
private theorem pairedSources_sound (values : A → Bool) :
    (sources : List A) → (start : Bool) → pairedSources sources = true →
      sources.foldl (fun bit key => xor bit (values key)) start = start
  | [], _, _ => rfl
  | head :: tail, start, verified => by
    by_cases paired : head ∈ tail
    · have rest : pairedSources (tail.erase head) = true := by
        simpa [pairedSources, paired] using verified
      rw [List.foldl_cons, fold_erase_xor values tail head paired]
      exact pairedSources_sound values (tail.erase head) start rest
    · simp [pairedSources, paired] at verified
termination_by sources _ _ => sources.length
decreasing_by
  exact Nat.lt_succ_of_le List.length_erase_le


end

/-- Identify an unconditional XOR's source at a resolved target bit. -/
def ResolvedInstruction.xorSource {n : Nat} (wire : Fin n) :
    ResolvedInstruction → Option (Fin n)
  | .xor source target => do
    let address ← (View.ofWires n source.length source).toOption
    let data ← (View.ofWires n source.length target).toOption
    let index ← (List.finRange source.length).find? fun i => data i == wire
    return address index
  | _ => none

theorem ResolvedInstruction.xorSource_sound {n : Nat} (snapshot : Snapshot)
    (calls : ReversibleOracle n) (step : ResolvedInstruction) (gate : ReversibleGate n)
    {wire source : Fin n} (lowered : step.compileReversible n snapshot calls = .ok gate)
    (found : step.xorSource wire = some source) (state : BasisWord n) :
    (gate.action state).readBit wire = (state.readBit wire ^^ state.readBit source) := by
  cases step <;> try contradiction
  rename_i inputs outputs
  simp only [xorSource, compileReversible, Bind.bind, Except.bind] at found lowered
  split at lowered
  · contradiction
  · rename_i address addressOk
    split at lowered
    · contradiction
    · rename_i data dataOk
      split at lowered
      · rename_i apart
        cases lowered
        simp only [addressOk, dataOk, Except.toOption, Option.bind_some] at found
        cases hit : (List.finRange inputs.length).find? (fun i => data i == wire) with
        | none => simp [hit, Option.bind] at found
        | some i =>
          have wireEq : data i = wire := beq_iff_eq.mp (List.find?_some (p := fun i => data i == wire) hit)
          have sourceEq : address i = source := by simpa [hit, Option.bind] using found
          rw [← wireEq, ← sourceEq]
          change (BasisWord.writeView data
            (Vector.ofFn fun j => state.readBit (data j) ^^ state.readBit (address j)) state).readBit
              (data i) = _
          rw [BasisWord.writeView_bit]
          simp [BasisWord.readBit]
      · contradiction

theorem ReversibleGate.flip_bit {n : Nat} (wire : Fin n) (state : BasisWord n) :
    ((ReversibleGate.flip wire).action state).readBit wire = (state.readBit wire ^^ true) := by
  let view := BasisWord.oneWire wire
  let index : Fin 1 := 0
  change (BasisWord.writeView view
    (Vector.ofFn fun i => !(BasisWord.readView view state).readBit i) state).readBit (view index) = _
  rw [BasisWord.writeView_bit]
  have projected : BasisWord.readBit (Vector.ofFn fun i => !(BasisWord.readView view state).readBit i) index =
      !(BasisWord.readView view state).readBit index := by
    simp [BasisWord.readBit]
  rw [projected, BasisWord.readView_bit]
  change (!(state.readBit wire)) = _
  cases state.readBit wire <;> rfl

theorem View.ofWires_single {n : Nat} (wire : Fin n) (view : View n 1)
    (resolved : View.ofWires n 1 [wire.val] = .ok view) : view 0 = wire := by
  unfold View.ofWires at resolved
  split at resolved
  · dsimp only at resolved
    split at resolved
    · split at resolved
      · cases resolved
        apply Fin.ext
        rfl
      · contradiction
    · contradiction
  · contradiction

theorem ResolvedInstruction.singleFlip_sound {n : Nat} (snapshot : Snapshot)
    (calls : ReversibleOracle n) (wire : Fin n) (gate : ReversibleGate n)
    (lowered : (ResolvedInstruction.unary .x [wire.val]).compileReversible n snapshot calls = .ok gate)
    (state : BasisWord n) :
    (gate.action state).readBit wire = (state.readBit wire ^^ true) := by
  simp only [ResolvedInstruction.compileReversible, List.length_cons, List.length_nil,
    Bind.bind, Except.bind] at lowered
  split at lowered
  · contradiction
  · rename_i view resolved
    cases lowered
    have target := View.ofWires_single wire view resolved
    change ((ReversibleGate.flips [view 0]).action state).readBit wire = _
    change ((ReversibleGate.flip (view 0)).action state).readBit wire = _
    rw [target, ReversibleGate.flip_bit]

def collectScratchToggles (n : Nat) (snapshot : Snapshot)
    (calls : ReversibleOracle n) (writes : Finset (Fin n)) (wire : Fin n) :
    List ResolvedInstruction → Except String (List (Option (Fin n)))
  | [] => .ok []
  | head :: tail => do
    let first ← head.compileReversible n snapshot calls
    let sources ← collectScratchToggles n snapshot calls writes wire tail
    if wire ∈ first.writes then
      if head = .unary .x [wire.val] then return none :: sources
      else
        let some source := head.xorSource wire | throw "Expected an unconditional XOR or flip"
        if source ∈ writes then throw "XOR source can be written"
        return some source :: sources
    else return sources

theorem collectScratchToggles_sound {n : Nat} (snapshot : Snapshot)
    (calls : ReversibleOracle n) (writes : Finset (Fin n)) (wire : Fin n)
    (steps : List ResolvedInstruction) (gate : ReversibleGate n) (sources : List (Option (Fin n)))
    (lowered : compileReversibleWord n snapshot calls steps = .ok gate)
    (bounds : gate.writes ⊆ writes)
    (collected : collectScratchToggles n snapshot calls writes wire steps = .ok sources)
    (state : BasisWord n) (values : Fin n → Bool)
    (fixed : ∀ i, i ∉ writes → state.readBit i = values i) :
    (gate.action state).readBit wire =
      sources.foldl (fun bit key => xor bit (key.elim true values)) (state.readBit wire) := by
  induction steps generalizing gate sources state with
  | nil =>
    cases lowered
    cases collected
    rfl
  | cons head tail ih =>
    simp only [compileReversibleWord, collectScratchToggles, Bind.bind, Except.bind] at lowered collected
    split at lowered
    · contradiction
    · rename_i first firstOk
      rw [firstOk] at collected
      split at lowered
      · contradiction
      · rename_i rest restOk
        cases lowered
        have firstWrites : first.writes ⊆ writes := Finset.subset_union_left.trans bounds
        have restWrites : rest.writes ⊆ writes := Finset.subset_union_right.trans bounds
        cases restSources : collectScratchToggles n snapshot calls writes wire tail with
        | error => simp [restSources] at collected
        | ok remaining =>
          have tailResult := ih rest remaining restOk restWrites restSources (first.action state)
            (fun pos stable => (first.same state pos (fun h => stable (firstWrites h))).trans (fixed pos stable))
          change (rest.action (first.action state)).readBit wire = _
          rw [tailResult]
          by_cases updated : wire ∈ first.writes
          · simp only [restSources, ite_eq_left updated] at collected
            by_cases flip : head = .unary .x [wire.val]
            · simp only [ite_eq_left flip, Pure.pure, Except.pure] at collected
              cases collected
              rw [List.foldl_cons, ResolvedInstruction.singleFlip_sound snapshot calls wire first
                (flip ▸ firstOk) state]
              rfl
            · simp only [ite_eq_right flip] at collected
              cases sourceOk : head.xorSource wire with
              | none => simp [sourceOk, throw] at collected
              | some source =>
                by_cases stable : source ∈ writes
                · simp [sourceOk, stable, throw] at collected
                · have result : some source :: remaining = sources := by
                    simpa [sourceOk, stable, Bind.bind, Except.bind, Pure.pure, Except.pure] using collected
                  rw [← result, List.foldl_cons,
                    head.xorSource_sound snapshot calls first firstOk sourceOk state]
                  change List.foldl _ (state.readBit wire ^^ state.readBit source) remaining =
                    List.foldl _ (state.readBit wire ^^ values source) remaining
                  rw [fixed source stable]
          · have same : remaining = sources := by
              simpa [restSources, updated, Pure.pure, Except.pure] using collected
            rw [same, first.same state wire updated]

def checkPairedToggles (n : Nat) (snapshot : Snapshot) (calls : ReversibleOracle n)
    (steps : List ResolvedInstruction) (writes : Finset (Fin n)) (wire : Fin n) : Bool :=
  match collectScratchToggles n snapshot calls writes wire steps with
  | .error _ => false
  | .ok sources => pairedSources sources

theorem checkPairedToggles_sound {n : Nat} (snapshot : Snapshot) (calls : ReversibleOracle n)
    (steps : List ResolvedInstruction) (gate : ReversibleGate n) (wire : Fin n)
    (compiled : compileReversibleWord n snapshot calls steps = .ok gate)
    (checked : checkPairedToggles n snapshot calls steps gate.writes wire = true)
    (state : BasisWord n) : (gate.action state).readBit wire = state.readBit wire := by
  unfold checkPairedToggles at checked
  split at checked
  · contradiction
  · rename_i sources collected
    rw [collectScratchToggles_sound snapshot calls gate.writes wire steps gate sources compiled
      Finset.Subset.rfl collected state state.readBit (fun _ _ => rfl)]
    exact pairedSources_sound (fun key => key.elim true state.readBit) sources _ checked

/-- Remove a candidate write from the footprint only after proving that its
unconditional flips and XORs from unchanged sources occur in pairs. -/
def narrowReversibleWrites {n : Nat} (snapshot : Snapshot) (calls : ReversibleOracle n)
    (steps : List ResolvedInstruction) (gate : ReversibleGate n)
    (compiled : compileReversibleWord n snapshot calls steps = .ok gate)
    (candidates : Fin n → Bool) : ReversibleGate n where
  action := gate.action
  writes := gate.writes.filter fun wire =>
    !(candidates wire && checkPairedToggles n snapshot calls steps gate.writes wire)
  support := gate.support
  writes_supported := (Finset.filter_subset _ _).trans gate.writes_supported
  same state wire absent := by
    by_cases original : wire ∈ gate.writes
    · have checked : candidates wire && checkPairedToggles n snapshot calls steps gate.writes wire = true := by
        simpa [original] using absent
      exact checkPairedToggles_sound snapshot calls steps gate wire compiled (Bool.and_eq_true_iff.mp checked).2 state
    · exact gate.same state wire original
  forward := gate.forward
  backward := gate.backward
  xorDependencies := gate.xorDependencies
  commutes := gate.commutes

end OracqVerify.RIR
