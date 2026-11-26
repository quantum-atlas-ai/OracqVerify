module

public import OracqVerify.RIR.WireTensor
public import OracqVerify.RIR.QRAMPhase
public import Qatlib.Foundations.PureStateMath.Reflection.Basic
public import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal

/-! Width- and iteration-parameterized denotation of a resolved Grover caller. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.WideGrover

open OracqVerify.RIR Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery Qatlib.Foundations.InstrumentCore.Measurement
open scoped Classical Matrix

def prefixPhase {n : Nat} (i : Fin n) : ResolvedInstruction :=
  if i.val = 0 then .unary .z [i.val]
  else .controlled ⟨List.range i.val, 0⟩ (.unary .z [i.val])

def prefixView {n k : Nat} (within : k ≤ n) : View n k :=
  ⟨Fin.castLE within, fun _ _ equal => Fin.ext (congrArg (Fin.val : Fin n → Nat) equal)⟩

theorem view_range {n k : Nat} (within : k ≤ n) :
    View.ofWires n k (List.range k) = .ok (prefixView within) := by
  unfold View.ofWires
  simp [List.getElem_range, Fin.ext_iff, Pure.pure, Except.pure, Nat.lt_of_lt_of_le _ within]
  exact Function.Embedding.ext fun _ => rfl

private theorem prefixMatches {n : Nat} (i : Fin n) (state : Reg n) :
    matchesGuard (prefixView i.isLt.le) 0 state ↔
      ∀ j : Fin n, j < i → state j = false := by
  constructor
  · intro h j before
    have bit := h ⟨j.val, before⟩
    have placed : prefixView i.isLt.le ⟨j.val, before⟩ = j := Fin.ext rfl
    rw [placed] at bit
    simpa only [Nat.zero_testBit] using bit
  · intro h j
    change state (Fin.castLE i.isLt.le j) = Nat.testBit 0 j.val
    simpa only [Nat.zero_testBit] using h (Fin.castLE i.isLt.le j) j.isLt

def FirstOne {n : Nat} (state : Reg n) (i : Fin n) : Prop :=
  (∀ j : Fin n, j < i → state j = false) ∧ state i = true

noncomputable def sign {n : Nat} (i : Fin n) (state : Reg n) : ℂ :=
  if FirstOne state i then -1 else 1

theorem prefixPhase_matrix {n : Nat} (i : Fin n) (memory : Snapshot) (oracle : Oracle n) :
    (prefixPhase i).matrixWith n memory oracle = .ok (diagonal (sign i)) := by
  have lower : GateAction.lower n false (.unary .z [i.val]) = .ok (.unary .z i false) := by
    simp [GateAction.lower, i.isLt]
  have atomic : (ResolvedInstruction.unary .z [i.val]).matrixWith n memory oracle =
      .ok (diagonal fun state : Reg n => if state i then (-1 : ℂ) else 1) := by
    change (ResolvedInstruction.unary .z [i.val]).matrix n memory = _
    rw [GateAction.lower_matrix memory lower]
    exact congrArg Except.ok (atWire_z n i)
  unfold prefixPhase
  split
  · rename_i first
    rw [atomic]
    congr 2
    funext state
    simp [sign, FirstOne, first, Fin.lt_def]
  · change (do
      let view ← View.ofWires n (List.range i.val).length (List.range i.val)
      let matrix ← (ResolvedInstruction.unary .z [i.val]).matrixWith n memory oracle
      pure (controlledMatrix (matchesGuard view 0) matrix)) = _
    rw [List.length_range, view_range i.isLt.le, atomic]
    change Except.ok (controlledMatrix _ _) = _
    rw [Except.ok.injEq]
    ext row col
    by_cases same : row = col
    · subst col
      by_cases active : ∀ j : Fin n, j < i → row j = false <;> cases bit : row i <;>
        simp [controlledMatrix, prefixMatches, sign, FirstOne, active, bit]
    · by_cases both : matchesGuard (prefixView i.isLt.le) 0 row ∧
        matchesGuard (prefixView i.isLt.le) 0 col <;>
        simp [controlledMatrix, both, same]

private theorem evalMap {A B : Type} (l : List A) (eval : A → Except String B) (values : A → B)
    (same : ∀ a ∈ l, eval a = .ok (values a)) :
    l.mapM eval = .ok (l.map values) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [List.mapM_cons, same a List.mem_cons_self,
      ih (fun b present => same b (List.mem_cons_of_mem a present)),
      Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem diagonal_word {n : Nat} {A : Type} (l : List A) (f : A → Reg n → ℂ) :
    wordMatrix (l.map fun a => diagonal (f a)) = diagonal (fun x => (l.map fun a => f a x).prod) := by
  induction l with
  | nil => simp [wordMatrix]
  | cons a tail ih =>
    rw [List.map_cons, wordMatrix, ih, diagonal_mul_diagonal]
    congr 1
    funext x
    simp [mul_comm]

private theorem firstUnique {n : Nat} {state : Reg n} {i j : Fin n} (a : FirstOne state i)
    (b : FirstOne state j) : i = j := by
  rcases lt_trichotomy i j with before | same | after
  · exact False.elim (Bool.noConfusion ((b.1 i before).symm.trans a.2))
  · exact same
  · exact False.elim (Bool.noConfusion ((a.1 j after).symm.trans b.2))

private theorem firstExists {n : Nat} {state : Reg n} (nonzero : state ≠ ZeroStr n) :
    ∃ i, FirstOne state i := by
  let ones : Finset (Fin n) := Finset.univ.filter fun i => state i = true
  have existsBit : ones.Nonempty := by
    by_contra! empty
    apply nonzero
    funext i
    have missing : i ∉ ones := by rw [empty]; exact Finset.notMem_empty i
    simpa [ones, ZeroStr] using missing
  let i := ones.min' existsBit
  have hit : state i = true := (Finset.mem_filter.mp (ones.min'_mem existsBit)).2
  refine ⟨i, fun j earlier => ?_, hit⟩
  have absent : state j ≠ true := fun set =>
    (not_le_of_gt earlier) (ones.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, set⟩))
  simpa using absent

def reflectionWord (n : Nat) : List ResolvedInstruction := (List.finRange n).map prefixPhase

theorem reflectionWord_matrix (n : Nat) (memory : Snapshot) (oracle : Oracle n) :
    ((reflectionWord n).mapM (ResolvedInstruction.matrixWith n memory oracle)).map wordMatrix =
      .ok (ZeroPhaseReflection n) := by
  classical
  unfold reflectionWord
  simp only [List.mapM_map, Function.comp_def]
  rw [evalMap _ _ (fun i => diagonal (sign i)) (fun i _ => prefixPhase_matrix i memory oracle)]
  change Except.ok (wordMatrix _) = _
  rw [diagonal_word]
  congr 2
  funext state
  rw [← List.ofFn_eq_map, Fin.prod_ofFn]
  by_cases zero : state = ZeroStr n
  · simp [zero, sign, FirstOne, ZeroStr]
  · obtain ⟨i, first⟩ := firstExists zero
    rw [Finset.prod_eq_single i]
    · simp [sign, first, zero]
    · intro j _ ne
      have notFirst : ¬ FirstOne state j := fun other => ne (firstUnique other first)
      simp [sign, notFirst]
    · simp

def target (w : Nat) : Reg (w+1) := fun i => decide (i = Fin.last w)

theorem target_iff (w : Nat) (state : Reg (w+1)) :
    FirstOne state (Fin.last w) ↔ state = target w := by
  constructor
  · intro found
    funext i
    by_cases last : i = Fin.last w
    · subst i
      simpa [target] using found.2
    · have earlier : i < Fin.last w := Fin.lt_last_iff_ne_last.mpr last
      simpa [target, last] using found.1 i earlier
  · rintro rfl
    exact ⟨fun i before => by simp [target, ne_of_lt before], by simp [target]⟩

noncomputable def oraclePhase {n : Nat} (marked : Reg n) : WireMatrix n :=
  diagonal fun x => if x = marked then -1 else 1

theorem oraclePhase_unitary {n : Nat} (marked : Reg n) :
    oraclePhase marked ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro state
  split <;> simp

theorem gate_matrix (w : Nat) (memory : Snapshot) (oracle : Oracle (w+1)) :
    (prefixPhase (Fin.last w)).matrixWith (w+1) memory oracle = .ok (oraclePhase (target w)) := by
  rw [prefixPhase_matrix]
  have diagonalEq : sign (Fin.last w) = fun x => if x = target w then -1 else 1 := by
    funext x
    simp [sign, target_iff]
  rw [diagonalEq]
  rfl

def invoke (n : Nat) (banks : List Resource) : ResolvedInstruction :=
  .query "grover_wide_mark" [List.range n] banks

def hadamards (n : Nat) : ResolvedInstruction := .unary .h (List.range n)

def round (n : Nat) (banks : List Resource) : List ResolvedInstruction :=
  [invoke n banks, hadamards n] ++ reflectionWord n ++ [hadamards n]

def caller (n : Nat) (banks : List Resource) (k : Nat) : List ResolvedInstruction :=
  hadamards n :: (List.replicate k (round n banks)).flatten

noncomputable def iterate {n : Nat} (marked : Reg n) (k : Nat) : WireMatrix n :=
  (Diffusion (Reg n) * oraclePhase marked) ^ k * HadamardN n

theorem iterate_unitary {n : Nat} (marked : Reg n) (k : Nat) :
    iterate marked k ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  mul_mem (pow_mem (mul_mem (diffusion_unitary Fintype.card_pos) (oraclePhase_unitary marked)) k)
    (hadamardN_unitary n)

noncomputable def evalWord (n : Nat) (s : Snapshot) (oracle : Oracle n)
    (steps : List ResolvedInstruction) : Except String (WireMatrix n) :=
  (steps.mapM (ResolvedInstruction.matrixWith n s oracle)).map wordMatrix

private theorem evalWord_append {n : Nat} (s : Snapshot) (oracle : Oracle n)
    {a b : List ResolvedInstruction} {u v : WireMatrix n}
    (first : evalWord n s oracle a = .ok u) (last : evalWord n s oracle b = .ok v) :
    evalWord n s oracle (a ++ b) = .ok (v * u) := by
  unfold evalWord at *
  cases ha : a.mapM (ResolvedInstruction.matrixWith n s oracle) <;>
    cases hb : b.mapM (ResolvedInstruction.matrixWith n s oracle) <;>
    simp [ha, hb, Except.map] at first last
  subst u
  subst v
  simp [List.mapM_append, ha, hb, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Except.map, wordMatrix_append]

private theorem evalWord_single {n : Nat} (s : Snapshot) (oracle : Oracle n)
    {i : ResolvedInstruction} {u : WireMatrix n} (checked : i.matrixWith n s oracle = .ok u) :
    evalWord n s oracle [i] = .ok u := by
  simp [evalWord, List.mapM_cons, checked, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Except.map, wordMatrix]

theorem caller_matrix {n : Nat} (s : Snapshot) (oracle : Oracle n) (banks : List Resource)
    (marked : Reg n) (k : Nat) (called : (invoke n banks).matrixWith n s oracle = .ok (oraclePhase marked)) :
    evalWord n s oracle (caller n banks k) = .ok (iterate marked k) := by
  have h := evalWord_single s oracle (allHadamards n s oracle)
  have reflection := reflectionWord_matrix n s oracle
  have step : evalWord n s oracle (round n banks) = .ok (Diffusion (Reg n) * oraclePhase marked) := by
    unfold round
    rw [diffusion_eq_hadamardN_zeroPhaseReflection]
    have tail := evalWord_append s oracle reflection h
    have computed := evalWord_append s oracle (evalWord_append s oracle (evalWord_single s oracle called) h) tail
    simpa only [List.append_assoc, List.singleton_append, Matrix.mul_assoc, hadamards] using computed
  have repeated (j : Nat) : evalWord n s oracle (List.replicate j (round n banks)).flatten =
      .ok ((Diffusion (Reg n) * oraclePhase marked) ^ j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [List.replicate_succ, List.flatten_cons, pow_succ]
      exact evalWord_append s oracle step ih
  exact evalWord_append s oracle h (repeated k)

theorem algorithmState {n : Nat} (marked : Reg n) (k : Nat) :
    iterate marked k *ᵥ Ket (ZeroStr n) = GroverState {marked} k := by
  have oracle : SetOracle {marked} = oraclePhase marked := by
    simp [SetOracle, PhaseOracle, oraclePhase]
  have runs (count : Nat) (state : QState (Reg n)) :
      Run (oraclePhase marked) (GroverCircuit (Reg n) count) state =
        (Diffusion (Reg n) * oraclePhase marked) ^ count *ᵥ state := by
    induction count generalizing state with
    | zero => simp [GroverCircuit, RepeatCircuit]
    | succ count ih =>
      rw [GroverCircuit, RepeatCircuit, run_append]
      change Run (oraclePhase marked) (GroverCircuit (Reg n) count)
        (Diffusion (Reg n) *ᵥ (oraclePhase marked *ᵥ state)) = _
      rw [ih, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [GroverState, oracle, runs, iterate, ← Matrix.mulVec_mulVec]
  exact congrArg (fun state => (Diffusion (Reg n) * oraclePhase marked) ^ k *ᵥ state)
    (applyGate_hadamardN_ket_zero n)

theorem successProbability {n : Nat} (positive : 0 < n) (marked : Reg n) (k : Nat) :
    let θ := Real.arcsin ((Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    MeasureProb (iterate marked k *ᵥ Ket (ZeroStr n)) {marked} =
      (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 := by
  let r := Real.sqrt ((2 : ℝ) ^ n)
  have rpos : 0 < r := by dsimp [r]; positivity
  have large : (1 : ℝ) < (2 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt positive)
  have rootLarge : 1 < r := by
    dsimp [r]
    rwa [Real.lt_sqrt (by norm_num), one_pow]
  have input : r⁻¹ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [inv_pos.mpr rpos], inv_lt_one_of_one_lt₀ rootLarge⟩
  have sine : Real.sin (Real.arcsin r⁻¹) = r⁻¹ :=
    Real.sin_arcsin (le_of_lt input.1) (le_of_lt input.2)
  dsimp only
  rw [algorithmState]
  apply measureProb_groverState Fintype.card_pos
  · rw [sine, inv_pow, Real.sq_sqrt (by positivity)]
    simp [Reg, one_div]
  · rw [sine]
    exact inv_ne_zero (ne_of_gt rpos)
  · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨Real.neg_pi_div_two_lt_arcsin.mpr input.1,
      Real.arcsin_lt_pi_div_two.mpr input.2⟩)

end OracqVerify.Verification.WideGrover
