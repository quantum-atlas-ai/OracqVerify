module

public import OracqVerify.RIR.ReversibleScope
public import Std.Data.HashMap.Lemmas

/-! Inputs supplied as hints only affect evaluation cost. Cached values are computed
by the same certified action, and every cache miss runs that action directly. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Std

structure BasisHints where
  forward : List Nat := []
  backward : List Nat := []
  deriving Lean.FromJson

def BasisWord.memoTable {n : Nat} (run : BasisWord n → BasisWord n) (inputs : List Nat) :
    HashMap (Array Bool) (BasisWord n) :=
  inputs.foldl (fun cache index =>
    let state := BasisWord.indexed n (Fin.ofNat (2 ^ n) index)
    cache.insert state.toArray (run state)) {}

private theorem BasisWord.memoTable_lookup {n : Nat} (run : BasisWord n → BasisWord n)
    (inputs : List Nat) (state : BasisWord n) :
    (memoTable run inputs)[state.toArray]? = none ∨
      (memoTable run inputs)[state.toArray]? = some (run state) := by
  unfold memoTable
  let update (cache : HashMap (Array Bool) (BasisWord n)) (index : Nat) :=
    let input := BasisWord.indexed n (Fin.ofNat (2 ^ n) index)
    cache.insert input.toArray (run input)
  change (inputs.foldl update {})[state.toArray]? = none ∨
    (inputs.foldl update {})[state.toArray]? = some (run state)
  have preserve (input : Nat) (cache : HashMap (Array Bool) (BasisWord n))
      (valid : cache[state.toArray]? = none ∨ cache[state.toArray]? = some (run state)) :
      (update cache input)[state.toArray]? = none ∨
        (update cache input)[state.toArray]? = some (run state) := by
    let x := BasisWord.indexed n (Fin.ofNat (2 ^ n) input)
    change (cache.insert x.toArray (run x))[state.toArray]? = none ∨
      (cache.insert x.toArray (run x))[state.toArray]? = some (run state)
    simp only [HashMap.getElem?_insert]
    split
    · rename_i eq
      have same : x = state := Vector.toArray_inj.mp (eq_of_beq eq)
      exact Or.inr (congrArg (fun word => some (run word)) same)
    · exact valid
  have folded (rest : List Nat) (cache : HashMap (Array Bool) (BasisWord n))
      (valid : cache[state.toArray]? = none ∨ cache[state.toArray]? = some (run state)) :
      (rest.foldl update cache)[state.toArray]? = none ∨
        (rest.foldl update cache)[state.toArray]? = some (run state) := by
    induction rest generalizing cache with
    | nil => exact valid
    | cons index rest ih => exact ih _ (preserve index cache valid)
  exact folded inputs {} (Or.inl HashMap.getElem?_empty)


/-- Keep the evaluated table in data captured by the callable action. -/
structure CachedBasisAction (n : Nat) where
  original : BasisWord n → BasisWord n
  table : HashMap (Array Bool) (BasisWord n)

def CachedBasisAction.apply {n : Nat} (cache : CachedBasisAction n)
    (state : BasisWord n) : BasisWord n :=
  match cache.table[state.toArray]? with
  | some output => output
  | none => cache.original state

@[noinline] def BasisWord.cacheRun {n : Nat} (run : BasisWord n → BasisWord n)
    (inputs : List Nat) : CachedBasisAction n :=
  ⟨run, memoTable run inputs⟩

theorem BasisWord.cacheRun_apply_eq {n : Nat} (run : BasisWord n → BasisWord n) (inputs : List Nat) :
    (cacheRun run inputs).apply = run := by
  funext state
  unfold cacheRun CachedBasisAction.apply
  dsimp only
  rcases memoTable_lookup run inputs state with miss | hit
  · rw [miss]
  · rw [hit]

def ReversibleGate.withHints {n : Nat} (gate : ReversibleGate n) (hints : BasisHints) :
    ReversibleGate n :=
  if hints.forward.isEmpty && hints.backward.isEmpty then gate
  else
    let forward := (BasisWord.cacheRun gate.action hints.forward).apply
    let backward := (BasisWord.cacheRun gate.action.symm hints.backward).apply
    have forwardEq : forward = gate.action := BasisWord.cacheRun_apply_eq gate.action hints.forward
    have backwardEq : backward = gate.action.symm := BasisWord.cacheRun_apply_eq gate.action.symm hints.backward
    { gate with
      action := ⟨forward, backward,
        by rw [forwardEq, backwardEq]; exact gate.action.left_inv,
        by rw [forwardEq, backwardEq]; exact gate.action.right_inv⟩
      same := by simpa only [Equiv.coe_fn_mk, forwardEq] using gate.same
      forward := by simpa only [Equiv.coe_fn_mk, forwardEq] using gate.forward
      backward := by simpa only [Equiv.symm_mk, Equiv.coe_fn_mk, backwardEq] using gate.backward
      commutes := by simpa only [Equiv.coe_fn_mk, forwardEq] using gate.commutes }

theorem ReversibleGate.withHints_matrix_eq {n : Nat} (gate : ReversibleGate n) (hints : BasisHints) :
    (gate.withHints hints).matrix = gate.matrix := by
  unfold ReversibleGate.withHints
  split
  · rfl
  · apply congrArg BasisWord.matrix
    apply Equiv.ext
    exact congrFun (BasisWord.cacheRun_apply_eq gate.action hints.forward)

end OracqVerify.RIR
