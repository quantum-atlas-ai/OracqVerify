module

public import OracqVerify.RIR.ScopedGateWord
public import OracqVerify.RIR.ScopedQRAM
public import OracqVerify.RIR.SnapshotImage
public import Qatlib.Foundations.PureStateMath.Reflection.Basic
public import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal

/-! An iteration-parameterized Grover caller on four addresses with interchangeable phase oracles. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.Grover

open RIR Lean Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open scoped Classical Matrix

def marked : Reg 2 := fun _ => true

def cz : ResolvedInstruction := .controlled ⟨[0], 1⟩ (.unary .z [1])

def roundWord (banks : List Resource) : List ResolvedInstruction :=
  [.query "grover_mark" [[0,1]] banks, .unary .h [0,1],
    .unary .z [0], .unary .z [1], cz, .unary .h [0,1]]

def callerWord (banks : List Resource) (iterations : Nat := 1) : List ResolvedInstruction :=
  .unary .h [0,1] :: (List.replicate iterations (roundWord banks)).flatten

noncomputable def phaseAt (target : Reg 2) : WireMatrix 2 :=
  diagonal fun x => if x = target then -1 else 1

noncomputable abbrev mark : WireMatrix 2 := phaseAt marked

noncomputable def iterateAt (target : Reg 2) (iterations : Nat := 1) : WireMatrix 2 :=
  (Diffusion (Reg 2) * phaseAt target) ^ iterations * HadamardN 2

noncomputable abbrev iterate : WireMatrix 2 := iterateAt marked

private def controlZero : View 2 1 :=
  (View.ofWires 2 1 [0]).toOption.get (by decide)

private theorem cz_matrix (memory : Snapshot) (oracle : Oracle 2) :
    cz.matrixWith 2 memory oracle = .ok mark := by
  change Except.ok (controlledMatrix (matchesGuard controlZero 1)
    (1 * atWire (1 : Fin 2) PauliZ)) = _
  rw [one_mul, Except.ok.injEq]
  ext r c
  have active (x : Reg 2) : matchesGuard controlZero 1 x ↔
      x 0 = true := by
    constructor
    · exact fun h => h 0
    · intro h i
      fin_cases i
      exact h
  have marked_iff (x : Reg 2) : x = marked ↔ x 0 = true ∧ x 1 = true := by
    rw [funext_iff, Fin.forall_fin_two]
    rfl
  by_cases eq : r = c
  · subst c
    simp only [controlledMatrix, active, phaseAt, diagonal_apply_eq, atWire,
      eq_self, implies_true, PauliZ, Matrix.one_apply, ite_true, and_self, marked_iff]
    cases h0 : r 0 <;> cases h1 : r 1 <;> simp [*]
  · rw [show mark = phaseAt marked from rfl, phaseAt, diagonal_apply_ne _ eq]
    unfold controlledMatrix
    split
    · unfold atWire
      split
      · rename_i other
        have diff : r 1 ≠ c 1 := fun same => eq (funext fun i => by
          by_cases hit : i = 1
          · simpa [hit] using same
          · exact other i hit)
        exact diagonal_apply_ne _ diff
      · rfl
    · simp [eq]

private theorem h_matrix (memory : Snapshot) (oracle : Oracle 2) :
    (ResolvedInstruction.unary .h [0,1]).matrixWith 2 memory oracle = .ok (HadamardN 2) := by
  change Except.ok ((1 * atWire (1 : Fin 2) Hadamard) * atWire (0 : Fin 2) Hadamard) = _
  rw [one_mul, Except.ok.injEq]
  ext r c
  let k : Reg 2 := ![r 0, c 1]
  have h1 (x y : Reg 2) : (∀ i, i ≠ (1 : Fin 2) → x i = y i) ↔ x 0 = y 0 := by
    rw [Fin.forall_fin_two]
    decide +revert
  have h0 (x y : Reg 2) : (∀ i, i ≠ (0 : Fin 2) → x i = y i) ↔ x 1 = y 1 := by
    rw [Fin.forall_fin_two]
    decide +revert
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp [atWire, h0, h1, k, HadamardN, Fin.prod_univ_two, mul_comm]
  · intro j _ diff
    by_cases left : r 0 = j 0
    · have right : j 1 ≠ c 1 := fun eq => diff (funext fun i => by
        fin_cases i
        · exact left.symm
        · exact eq)
      simp [atWire, h0, right]
    · simp [atWire, h1, left]
  · simp

private theorem phaseWire (i : Fin 2) :
    atWire i PauliZ = diagonal (fun x => if x i then (-1 : ℂ) else 1) := by
  ext r c
  by_cases same : r = c
  · subst c
    simp [atWire, PauliZ]
  · rw [diagonal_apply_ne _ same]
    unfold atWire
    split
    · rename_i other
      have dif : r i ≠ c i := fun eq => same (funext fun j => by
        by_cases hit : j = i
        · simpa [hit] using eq
        · exact other j hit)
      exact diagonal_apply_ne _ dif
    · rfl

private theorem reflection : mark * (atWire (1 : Fin 2) PauliZ * atWire (0 : Fin 2) PauliZ) =
    ZeroPhaseReflection 2 := by
  rw [phaseWire, phaseWire]
  simp only [phaseAt, diagonal_mul_diagonal]
  unfold ZeroPhaseReflection
  congr 1
  funext x
  have eq (value : Bool) : x = (fun _ => value) ↔ x 0 = value ∧ x 1 = value := by
    rw [funext_iff, Fin.forall_fin_two]
  change (if x = marked then (-1 : ℂ) else 1) *
    ((if x 1 then (-1 : ℂ) else 1) * (if x 0 then (-1 : ℂ) else 1)) =
    if x = ZeroStr 2 then 1 else -1
  unfold marked ZeroStr
  simp only [eq true, eq false]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [*]

private theorem roundMatrix (memory : Snapshot) (oracle : Oracle 2) (banks : List Resource)
    (target : Reg 2) (call : oracle ⟨"grover_mark", [[0,1]], banks⟩ = .ok (phaseAt target)) :
    ∃ word, (roundWord banks).mapM (ResolvedInstruction.matrixWith 2 memory oracle) = .ok word ∧
      wordMatrix word = Diffusion (Reg 2) * phaseAt target := by
  have query : (ResolvedInstruction.query "grover_mark" [[0,1]] banks).matrixWith 2 memory oracle =
      .ok (phaseAt target) := call
  have z0 : (ResolvedInstruction.unary .z [0]).matrixWith 2 memory oracle =
      .ok (1 * atWire (0 : Fin 2) PauliZ) := rfl
  have z1 : (ResolvedInstruction.unary .z [1]).matrixWith 2 memory oracle =
      .ok (1 * atWire (1 : Fin 2) PauliZ) := rfl
  refine ⟨[phaseAt target, HadamardN 2, atWire 0 PauliZ, atWire 1 PauliZ, mark, HadamardN 2], ?_, ?_⟩
  · simp only [roundWord, List.mapM_cons, List.mapM_nil, h_matrix, cz_matrix, query, z0, z1,
      Bind.bind, Except.bind, Pure.pure, Except.pure, one_mul]
  · rw [diffusion_eq_hadamardN_zeroPhaseReflection, ← reflection]
    simp only [wordMatrix, one_mul, mul_assoc]

private theorem callerMatrix (memory : Snapshot) (oracle : Oracle 2) (banks : List Resource)
    (target : Reg 2) (iterations : Nat)
    (call : oracle ⟨"grover_mark", [[0,1]], banks⟩ = .ok (phaseAt target)) :
    ((callerWord banks iterations).mapM (ResolvedInstruction.matrixWith 2 memory oracle)).map wordMatrix =
      .ok (iterateAt target iterations) := by
  obtain ⟨word, evaluated, round⟩ := roundMatrix memory oracle banks target call
  have repeatWord (count : Nat) :
      ((List.replicate count (roundWord banks)).flatten).mapM
          (ResolvedInstruction.matrixWith 2 memory oracle) =
        .ok (List.replicate count word).flatten := by
    induction count with
    | zero => rfl
    | succ count ih =>
      simp [List.replicate_succ, List.mapM_append, evaluated, ih, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  have repeatMatrix (count : Nat) :
      wordMatrix (List.replicate count word).flatten =
        (Diffusion (Reg 2) * phaseAt target) ^ count := by
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [List.replicate_succ, List.flatten_cons, wordMatrix_append, round, ih, pow_succ]
  simp only [callerWord, List.mapM_cons, h_matrix, repeatWord, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Except.map, wordMatrix, repeatMatrix, iterateAt]

private theorem phase_unitary (target : Reg 2) : phaseAt target ∈ unitaryGroup (Reg 2) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  split <;> simp

private theorem iterate_unitary (target : Reg 2) (iterations : Nat) :
    iterateAt target iterations ∈ unitaryGroup (Reg 2) ℂ :=
  (unitaryGroup _ _).mul_mem (pow_mem ((unitaryGroup _ _).mul_mem
    (diffusion_unitary Fintype.card_pos) (phase_unitary target)) iterations) (hadamardN_unitary 2)

/-- Search on four addresses with one marked address is exact after one iterate. -/
theorem exact_readout_at (target : Reg 2) : iterateAt target *ᵥ Ket (ZeroStr 2) = Ket target := by
  have card : Fintype.card (Reg 2) = 4 := by simp [Reg]
  have amplitude : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = 1 / 2 := by rw [inv_pow, sqrt2_sq, one_div]
  have initial : HadamardN 2 *ᵥ Ket (ZeroStr 2) = fun _ => (1 / 2 : ℂ) := by
    funext x
    simp [Matrix.mulVec, dotProduct, Ket, hadamardN_apply_zero_right, amplitude]
  let phase := fun x : Reg 2 => if x = target then (-1 / 2 : ℂ) else 1 / 2
  have phased : phaseAt target *ᵥ (fun _ => (1 / 2 : ℂ)) = phase := by
    funext x
    rw [phaseAt, mulVec_diagonal]
    by_cases eq : x = target <;> simp [phase, eq, div_eq_mul_inv]
  have phaseSum : ∑ x, phase x = 1 := by
    have point (x : Reg 2) : phase x = 1 / 2 - Ket target x := by
      by_cases eq : x = target
      · norm_num [phase, Ket, eq]
      · simp [phase, Ket, eq]
    simp only [point, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card, Ket]
    norm_num
  rw [iterateAt, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, initial, phased]
  funext x
  change ApplyGate (Diffusion (Reg 2)) phase x = Ket target x
  rw [applyGate_diffusion, phaseSum, card]
  by_cases same : x = target <;> simp [phase, Ket, same] <;> norm_num

theorem exact_readout : iterate *ᵥ Ket (ZeroStr 2) = Ket marked := exact_readout_at marked

open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- Identify the decoded caller's state with Qatlib's search algorithm for every iteration count. -/
theorem algorithmState (target : Reg 2) (iterations : Nat) :
    iterateAt target iterations *ᵥ Ket (ZeroStr 2) = GroverState {target} iterations := by
  have oracle : SetOracle {target} = phaseAt target := by
    simp [SetOracle, PhaseOracle, phaseAt]
  have runs (count : Nat) (state : QState (Reg 2)) :
      Run (phaseAt target) (GroverCircuit (Reg 2) count) state =
        (Diffusion (Reg 2) * phaseAt target) ^ count *ᵥ state := by
    induction count generalizing state with
    | zero => simp [GroverCircuit, RepeatCircuit]
    | succ count ih =>
      rw [GroverCircuit, RepeatCircuit, run_append]
      change Run (phaseAt target) (GroverCircuit (Reg 2) count)
        (Diffusion (Reg 2) *ᵥ (phaseAt target *ᵥ state)) = _
      rw [ih, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [GroverState, oracle, runs, iterateAt, ← Matrix.mulVec_mulVec]
  exact congrArg (fun state => (Diffusion (Reg 2) * phaseAt target) ^ iterations *ᵥ state)
    (applyGate_hadamardN_ket_zero 2)

open Qatlib.Foundations.InstrumentCore.Measurement

theorem successProbability (target : Reg 2) (iterations : Nat) :
    MeasureProb (iterateAt target iterations *ᵥ Ket (ZeroStr 2)) {target} =
      (Real.sin ((2 * (iterations : ℝ) + 1) * (Real.pi / 6))) ^ 2 := by
  rw [algorithmState]
  apply measureProb_groverState Fintype.card_pos
  · norm_num [Real.sin_pi_div_six, Reg]
  · norm_num [Real.sin_pi_div_six]
  · rw [Real.cos_pi_div_six]
    positivity

inductive Implementation
  | gate | qram
  deriving DecidableEq

abbrev Implementation.isQram : Implementation → Bool
  | .gate => false
  | .qram => true

def entryBank : Resource := ⟨"marks", ⟨2, 1⟩⟩
def passedBank : Resource := ⟨"capture_e3d11da4dd6ea5b4", ⟨2, 1⟩⟩
def lookupBank : Resource := ⟨"lookup", ⟨2, 1⟩⟩

def Implementation.plan : Implementation → ScopedCapturePlan
  | .gate => []
  | .qram => [("grover_two_bits", [("grover_mark", [.captured entryBank])])]

def banksFor (implementation : Implementation) (bank : Resource) : List Resource :=
  if implementation.isQram then [bank] else []

def peak (implementation : Implementation) : Nat := if implementation.isQram then 1 else 0

def qramWord : List ResolvedInstruction :=
  [.load lookupBank [0,1] [2], .unary .z [2], .load lookupBank [0,1] [2]]

def leaf (impl : Implementation) : ScopedModule :=
  ⟨if impl.isQram then "mark_with_qram" else "mark_with_gate", 2, peak impl,
    banksFor impl lookupBank, some (if impl.isQram then qramWord else [cz]), peak impl, true, true⟩

def wrapper (impl : Implementation) : ScopedModule :=
  let banks := banksFor impl passedBank
  ⟨"grover_mark", 2, 0, banks, some [.query (leaf impl).name [[0,1]] banks], peak impl, true, true⟩

def root (impl : Implementation) (iterations : Nat := 1) : ScopedModule :=
  let banks := banksFor impl entryBank
  ⟨"grover_two_bits", 2, 0, banks, some (callerWord banks iterations), peak impl, true, true⟩

def expected (impl : Implementation) (iterations : Nat := 1) : ScopedProgram :=
  ⟨"grover_two_bits", [leaf impl, wrapper impl, root impl iterations], 2, peak impl⟩

def openGraph (iterations : Nat := 1) : ScopedProgram :=
  ⟨"grover_two_bits", [⟨"grover_mark", 2, 0, [], none, 0, true, true⟩, root .gate iterations], 2, 0⟩

def targetAt (index : Fin 4) : Reg 2 := (orderedBitsIndex 2).symm index

def tableAt (index : Fin 4) : BankImage 2 1 where
  words := Vector.ofFn fun address => if address = index then 1 else 0
  fits := by
    intro address
    rw [Vector.getElem_ofFn]
    split <;> decide

private theorem target_last : targetAt 3 = marked := by decide

def table : BankImage 2 1 := tableAt 3

private def qramRead : ResolvedRead 3 :=
  (ResolvedRead.create 3 lookupBank [0,1] [2]).toOption.get (by decide)

private theorem leaf_gate (memory : Snapshot) : (leaf .gate).interpret [] memory = .ok mark := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (phase_unitary marked)
  change (([cz].mapM (ResolvedInstruction.matrixWith 2 memory (ScopedEnvironment.atCall [] 2 memory))).map
    wordMatrix) = _
  simp [cz_matrix, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, wordMatrix]

private theorem leaf_qram (index : Fin 4) (memory : Snapshot)
    (supplied : memory lookupBank = some (tableAt index).bank) :
    (leaf .qram).interpret [] memory = .ok (phaseAt (targetAt index)) := by
  have evaluated := scopedQramPhase_interpret (leaf .qram) qramRead [0,1] [2] rfl
    ⟨0, by decide⟩ ⟨0, by decide⟩ rfl rfl [] memory (tableAt index).bank supplied
  rw [evaluated]
  change Except.ok (diagonal (fun address : Reg 2 =>
    if (tableAt index).bank ((appendZero 2 1 address) ∘ qramRead.address) 0 then (-1 : ℂ) else 1)) =
    Except.ok (phaseAt (targetAt index))
  rw [Except.ok.injEq]
  unfold phaseAt
  congr 1
  funext address
  have reads : (tableAt index).bank ((appendZero 2 1 address) ∘ qramRead.address) 0 =
      decide (address = targetAt index) := by
    fin_cases index <;> decide +revert
  rw [reads]
  simp

private theorem wholeCall {environment : ScopedEnvironment} {name : String}
    {formals actuals : List Resource} {denote : Snapshot → Except String (WireMatrix 2)}
    {memory child : Snapshot} {u : WireMatrix 2} (found : lookup environment name "scoped callee" = .ok ⟨2, formals, denote⟩)
    (forwarded : memory.forward formals actuals = .ok child) (computed : denote child = .ok u) :
    environment.atCall 2 memory ⟨name, [[0,1]], actuals⟩ = .ok u := by
  unfold ScopedEnvironment.atCall
  simp only [found, Bind.bind, Except.bind]
  rw [show [[0,1]].flatten = List.range 2 by decide, View.ofWires_range]
  simp [forwarded, computed, Pure.pure, Except.pure, View.placeMatrix_refl]

private def tableSnapshot (bank : Resource)
    (value : ReadOnlyQRAM.Bank bank.type.addressWidth bank.type.dataWidth) : Snapshot :=
  fun r => if h : bank = r then some (h ▸ value) else none

private theorem forwardOne (formal actual : Resource) (shape : formal.type = actual.type)
    (memory : Snapshot) (value : ReadOnlyQRAM.Bank actual.type.addressWidth actual.type.dataWidth)
    (found : memory actual = some value) :
    memory.forward [formal] [actual] = .ok (tableSnapshot formal (shape.symm ▸ value)) := by
  unfold Snapshot.forward
  simp only [List.map_cons, List.map_nil, shape, ite_true]
  congr 1
  funext r
  by_cases eq : formal = r
  · subst r
    simp [tableSnapshot, shape, found, Eq.symm]
    cases formal with
    | mk formalName formalType =>
      cases actual with
      | mk actualName actualType =>
        change formalType = actualType at shape
        subst actualType
        rfl
  · simp [tableSnapshot, eq]

private theorem wrapper_matrix (impl : Implementation) (index : Fin 4) (memory : Snapshot)
    (gateIndex : impl = .gate → index = 3)
    (supplied : impl = .qram → memory passedBank = some (tableAt index).bank) :
    (wrapper impl).interpret (scopedEnvironment [leaf impl] [] unboundScopedOracle) memory = .ok (phaseAt (targetAt index)) := by
  let banks := banksFor impl passedBank
  let known := scopedEnvironment [leaf impl] [] unboundScopedOracle
  have found : lookup known (leaf impl).name "scoped callee" =
      .ok ⟨2, (leaf impl).banks, (leaf impl).interpret []⟩ := by
    cases impl <;> rfl
  have called : known.atCall 2 memory ⟨(leaf impl).name, [[0,1]], banks⟩ = .ok (phaseAt (targetAt index)) := by
    cases impl with
    | gate =>
      rw [gateIndex rfl, target_last]
      exact wholeCall found rfl (leaf_gate emptySnapshot)
    | qram =>
      have forwarded := forwardOne lookupBank passedBank rfl memory (tableAt index).bank (supplied rfl)
      exact wholeCall found forwarded (leaf_qram index _ (by simp [tableSnapshot]; rfl))
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (phase_unitary (targetAt index))
  change (([ResolvedInstruction.query (leaf impl).name [[0,1]] banks].mapM
    (ResolvedInstruction.matrixWith 2 memory (known.atCall 2 memory))).map wordMatrix) = _
  simp [ResolvedInstruction.matrixWith, called, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, wordMatrix]

noncomputable def phaseSpec (target : Reg 2) (valid : Snapshot → Prop) : ScopedOracle :=
  fun name width memory =>
    if same : 2 = width then
      if name = "grover_mark" ∧ valid memory then .ok (same ▸ phaseAt target)
      else .error "Grover oracle specification does not apply"
    else .error "Grover oracle requires two wires"

private theorem phaseSpec_valid (target : Reg 2) (valid : Snapshot → Prop) (memory : Snapshot)
    (ok : valid memory) : phaseSpec target valid "grover_mark" 2 memory = .ok (phaseAt target) := by
  simp [phaseSpec, ok]

private theorem phaseSpec_refines (target : Reg 2) (valid : Snapshot → Prop)
    (denote : ScopedMeaning (wrapper .gate))
    (realizes : ∀ memory, valid memory → denote memory = .ok (phaseAt target)) :
    ∀ memory, ScopedRefines (phaseSpec target valid "grover_mark" 2 memory) (denote memory) := by
  intro memory result computed
  by_cases ok : valid memory
  · rw [phaseSpec_valid target valid memory ok] at computed
    cases computed
    exact realizes memory ok
  · simp [phaseSpec, ok] at computed

private theorem slotContracts (impl : Implementation) (index : Fin 4)
    (gateIndex : impl = .gate → index = 3) (iterations : Nat) :
    ScopedContracts ["grover_mark"]
      (phaseSpec (targetAt index) (fun memory => impl = .qram → memory passedBank = some (tableAt index).bank))
      [] (expected impl iterations).modules := by
  cases impl <;>
    simp only [expected, ScopedContracts, leaf, wrapper, root, Implementation.isQram,
      Bool.false_eq_true, ite_true, ite_false, List.contains_cons, List.contains_nil,
      String.reduceBEq, Bool.or_false, IsEmpty.forall_iff, true_and, and_true]
  · intro _
    exact phaseSpec_refines (targetAt index) _ _ (fun memory ok => wrapper_matrix .gate index memory gateIndex ok)
  · intro _
    exact phaseSpec_refines (targetAt index) _ _ (fun memory ok => wrapper_matrix .qram index memory gateIndex (fun _ => ok trivial))

private theorem caller_interpret (impl : Implementation) (memory : Snapshot) (target : Reg 2)
    (iterations : Nat) (known : ScopedEnvironment)
    (called : known.atCall 2 memory ⟨"grover_mark", [[0,1]], banksFor impl entryBank⟩ =
      .ok (phaseAt target)) :
    (root impl iterations).interpret known memory = .ok (iterateAt target iterations) := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (iterate_unitary target iterations)
  exact callerMatrix memory (known.atCall 2 memory) (banksFor impl entryBank) target iterations called

private theorem abstract_matrix (impl : Implementation) (index : Fin 4) (memory : Snapshot) (iterations : Nat)
    (supplied : impl = .qram → memory entryBank = some (tableAt index).bank) :
    (expected impl iterations).matrixWith memory ["grover_mark"]
      (phaseSpec (targetAt index) (fun m => impl = .qram → m passedBank = some (tableAt index).bank)) = .ok (iterateAt (targetAt index) iterations) := by
  let valid : Snapshot → Prop := fun m => impl = .qram → m passedBank = some (tableAt index).bank
  let spec := phaseSpec (targetAt index) valid
  let known := scopedEnvironment [leaf impl, wrapper impl] ["grover_mark"] spec
  have found : lookup known "grover_mark" "scoped callee" =
      .ok ⟨2, banksFor impl passedBank, spec "grover_mark" 2⟩ := by cases impl <;> rfl
  have called : known.atCall 2 memory ⟨"grover_mark", [[0,1]], banksFor impl entryBank⟩ =
      .ok (phaseAt (targetAt index)) := by
    cases impl with
    | gate =>
      apply wholeCall found (child := emptySnapshot) rfl
      change phaseSpec (targetAt index) (fun m => Implementation.gate = .qram → m passedBank = some (tableAt index).bank)
        "grover_mark" 2 emptySnapshot = _
      simp [phaseSpec]
    | qram =>
      have forwarded := forwardOne passedBank entryBank rfl memory (tableAt index).bank (supplied rfl)
      apply wholeCall found forwarded
      change phaseSpec (targetAt index) (fun m => Implementation.qram = .qram → m passedBank = some (tableAt index).bank)
        "grover_mark" 2 (tableSnapshot passedBank (tableAt index).bank) = _
      have loaded : tableSnapshot passedBank (tableAt index).bank passedBank = some (tableAt index).bank := by
        simp [tableSnapshot]; rfl
      exact phaseSpec_valid (targetAt index) _ _ (fun _ => loaded)
  have interpreted := caller_interpret impl memory (targetAt index) iterations known called
  have foundRoot : lookup (scopedEnvironment (expected impl iterations).modules ["grover_mark"] spec)
      (expected impl iterations).entry "scoped entry" = .ok ⟨2, (root impl iterations).banks, (root impl iterations).interpret known⟩ := by
    cases impl <;> rfl
  change (expected impl iterations).matrixWith memory ["grover_mark"] spec = _
  unfold ScopedProgram.matrixWith
  dsimp only
  rw [foundRoot]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, interpreted, show (expected impl iterations).entryWires = 2 from rfl]

theorem open_matrix (memory : Snapshot) (target : Reg 2) (iterations : Nat := 1) :
    (openGraph iterations).matrixWith memory ["grover_mark"] (phaseSpec target (fun _ => True)) =
      .ok (iterateAt target iterations) := by
  let spec := phaseSpec target (fun _ => True)
  let known := scopedEnvironment [⟨"grover_mark", 2, 0, [], none, 0, true, true⟩] ["grover_mark"] spec
  have found : lookup known "grover_mark" "scoped callee" = .ok ⟨2, [], spec "grover_mark" 2⟩ := rfl
  have called : known.atCall 2 memory ⟨"grover_mark", [[0,1]], []⟩ = .ok (phaseAt target) :=
    wholeCall found (child := emptySnapshot) rfl (by simp [spec, phaseSpec])
  have interpreted := caller_interpret .gate memory target iterations known called
  have foundRoot : lookup (scopedEnvironment (openGraph iterations).modules ["grover_mark"] spec)
      (openGraph iterations).entry "scoped entry" = .ok ⟨2, [], (root .gate iterations).interpret known⟩ := rfl
  change (openGraph iterations).matrixWith memory ["grover_mark"] spec = _
  unfold ScopedProgram.matrixWith
  dsimp only
  rw [foundRoot]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, interpreted, show (openGraph iterations).entryWires = 2 from rfl]

structure Certificate (original bound : Program) (image : Json) (impl : Implementation) (index : Fin 4) (iterations : Nat := 1) where
  link : ScopedSourceLink original bound impl.plan
  caller : link.caller = openGraph iterations
  closed : link.closed = expected impl iterations
  gateIndex : impl = .gate → index = 3
  tableChecked : impl = .qram → image.getObjValAs? (Array Nat) "marks" = .ok (tableAt index).words.toArray

def certifyAt (original bound : Program) (image : Json) (impl : Implementation) (index : Fin 4)
    (iterations : Nat := 1) : Except String (Certificate original bound image impl index iterations) := do
  let link ← verifyScopedSourceLink original bound impl.plan
  if caller : link.caller = openGraph iterations then
    if closed : link.closed = expected impl iterations then
      match which : impl with
      | .gate =>
        if same : index = 3 then
          return ⟨link, caller, closed, fun _ => same, fun eq => by rw [which] at eq; cases eq⟩
        else throw "The CZ implementation marks index 3"
      | .qram =>
        if tableChecked : image.getObjValAs? (Array Nat) "marks" = .ok (tableAt index).words.toArray then
          return ⟨link, caller, closed, (fun eq => by rw [which] at eq; cases eq), fun _ => tableChecked⟩
        else throw s!"Grover expects a single marked address at index {index.val}"
    else throw "Unexpected bound Grover body or oracle"
  else throw "Unexpected open Grover caller"

def certify (original bound : Program) (image : Json) (impl : Implementation) :
    Except String (Certificate original bound image impl 3) :=
  certifyAt original bound image impl 3

/-- Both independently decoded bindings execute the same Grover matrix on the public register. -/
theorem Certificate.sound {original bound : Program} {image : Json} {impl : Implementation} {index : Fin 4} {iterations : Nat}
    (cert : Certificate original bound image impl index iterations) :
    ∃ memory : Snapshot, cert.link.closed.decodeSnapshot image = .ok memory ∧
      bound.scopedMatrix memory = .ok ⟨2, iterateAt (targetAt index) iterations⟩ := by
  let spec := phaseSpec (targetAt index) (fun m => impl = .qram → m passedBank = some (tableAt index).bank)
  have slots : scopedSlots cert.link.caller = ["grover_mark"] := by rw [cert.caller]; rfl
  have exposed : cert.link.exposed = (expected impl iterations).hideSlots ["grover_mark"] := by
    rw [cert.link.checked, slots, cert.closed]
  have contracts : ScopedContracts (scopedSlots cert.link.caller) spec [] cert.link.closed.modules := by
    rw [slots, cert.closed]
    exact slotContracts impl index cert.gateIndex iterations
  have lift (memory : Snapshot) (supplied : impl = .qram → memory entryBank = some (tableAt index).bank) :
      bound.scopedMatrix memory = .ok ⟨2, iterateAt (targetAt index) iterations⟩ := by
    have width : cert.link.exposed.entryWires = 2 := by rw [exposed]; rfl
    have exec : cert.link.exposed.matrixWith memory (scopedSlots cert.link.caller) spec =
        .ok (width.symm ▸ iterateAt (targetAt index) iterations) := by
      simp only [slots]
      generalize cert.link.exposed = graph at exposed width ⊢
      subst graph
      rw [ScopedProgram.hideSlots_matrix]
      exact abstract_matrix impl index memory iterations supplied
    have result := cert.link.sound memory spec contracts exec
    have pack {n : Nat} (w : n = 2) :
        (⟨n, w.symm ▸ iterateAt (targetAt index) iterations⟩ : Σ n, WireMatrix n) = ⟨2, iterateAt (targetAt index) iterations⟩ := by subst n; rfl
    simpa only [pack width] using result
  rw [cert.closed]
  cases impl with
  | gate =>
    refine ⟨emptySnapshot, rfl, lift emptySnapshot (by intro eq; cases eq)⟩
  | qram =>
    let memory := tableSnapshot entryBank (tableAt index).bank
    have words := cert.tableChecked rfl
    have loaded : (expected .qram iterations).decodeSnapshot image = .ok memory := by
      have found : lookup ((expected .qram iterations).modules.map fun m => (m.name, m))
          (expected .qram iterations).entry "scoped entry" = .ok (root .qram iterations) := rfl
      have imageEq : BankImage.decode entryBank image = .ok (tableAt index) := by
        unfold BankImage.decode
        rw [show entryBank.name = "marks" from rfl]
        simp only [words, Bind.bind, Except.bind]
        have size := (tableAt index).words.size_toArray
        have validSize : 2 ^ 2 = 2 ^ entryBank.type.addressWidth := rfl
        simp only [size, dite_eq_left validSize]
        have fits : ∀ address : Fin 4, (tableAt index).words[address.val] < 2 := (tableAt index).fits
        split
        · rfl
        · rename_i bad
          exact (bad fits).elim
      unfold ScopedProgram.decodeSnapshot
      rw [found]
      simp [root, banksFor, List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure,
        imageEq, memory]
      rfl
    exact ⟨memory, loaded, lift memory (by intro _; simp [memory, tableSnapshot]; rfl)⟩

/-- The accepted decoded circuit prepares the marked basis state from a zero register. -/
theorem Certificate.readout {original bound : Program} {image : Json} {impl : Implementation} {index : Fin 4}
    (cert : Certificate original bound image impl index) :
    ∃ (memory : Snapshot) (u : WireMatrix 2),
      cert.link.closed.decodeSnapshot image = .ok memory ∧
      bound.scopedMatrix memory = .ok ⟨2, u⟩ ∧ u *ᵥ Ket (ZeroStr 2) = Ket (targetAt index) := by
  obtain ⟨memory, decoded, matrix⟩ := cert.sound
  exact ⟨memory, iterateAt (targetAt index), decoded, matrix, exact_readout_at (targetAt index)⟩

theorem Certificate.probability {original bound : Program} {image : Json} {impl : Implementation}
    {index : Fin 4} {iterations : Nat} (cert : Certificate original bound image impl index iterations) :
    ∃ (memory : Snapshot) (u : WireMatrix 2),
      cert.link.closed.decodeSnapshot image = .ok memory ∧
      bound.scopedMatrix memory = .ok ⟨2, u⟩ ∧
      MeasureProb (u *ᵥ Ket (ZeroStr 2)) {targetAt index} =
        (Real.sin ((2 * (iterations : ℝ) + 1) * (Real.pi / 6))) ^ 2 := by
  obtain ⟨memory, decoded, matrix⟩ := cert.sound
  exact ⟨memory, iterateAt (targetAt index) iterations, decoded, matrix,
    successProbability (targetAt index) iterations⟩

end OracqVerify.Verification.Grover
