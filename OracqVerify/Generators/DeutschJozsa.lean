module

public import OracqVerify.RIR.Resolve
public import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-! Generate open Deutsch–Jozsa RIR and prove its semantics after resolving its call and views. -/

set_option warningAsError true

public section

namespace OracqVerify.Generators.DeutschJozsa

open Lean OracqVerify.RIR
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-- The logical instructions around the unique oracle call in the resolved entry. -/
def resolvedDJ (width : Nat) (oracle : List ResolvedInstruction) : ResolvedProgram :=
  ⟨width + 1, [.unary .x [width], .unary .h [width], .unary .h (List.range width)] ++
    oracle ++ [.unary .h (List.range width)]⟩

/-- The logical call retains the slot name and the ordered input and answer wires. -/
def query (width : Nat) (banks : List Resource := []) : ResolvedInstruction :=
  .query "dj_function" [List.range width, [width]] banks

/-- Build one symbolic query with the standard Boolean XOR interface. -/
def generate (width : Nat) : Program :=
  let input := bitsRef "input" width
  let answer := bitsRef "answer" 1
  let entry : RIR.Module :=
    { name := "deutsch_jozsa"
      registers := [⟨"input", ⟨.bits, width⟩⟩, ⟨"answer", ⟨.bits, 1⟩⟩]
      resources := []
      body := some [.unary .x answer, .unary .h answer, .unary .h input,
        .call "dj_function" [input, answer] [], .unary .h input]
      attributes := [("algorithm", .str "deutsch_jozsa"),
        ("readout_register", .str "input"), ("validation_stage", .str "paradigm")] }
  let oracle : RIR.Module :=
    { name := "dj_function"
      registers := [⟨"address", ⟨.bits, width⟩⟩, ⟨"data", ⟨.bits, 1⟩⟩]
      resources := []
      body := none
      attributes := [("implementation_status", .str "unresolved"),
        ("oracle_paradigm", .str "database_xor"),
        ("supports_adjoint", .bool true), ("supports_controlled", .bool true)] }
  ⟨entry.name, [entry, oracle]⟩

private noncomputable def toStep (width : Nat) (instruction : ResolvedInstruction) :
    Except String (Step (Reg width × Bool)) := do
  match instruction with
  | .unary .x wires =>
    unless wires = [width] do throw "Expected X on the answer wire"
    return .gate (TensorGate 1 PauliX)
  | .unary .h wires =>
    if wires = [width] then return .gate (TensorGate 1 Hadamard)
    if wires = List.range width then return .gate (LiftGate (HadamardN width))
    throw "Expected H on the full input or on the answer wire"
  | .query slot arguments banks =>
    unless slot = "dj_function" ∧ arguments = [List.range width, [width]] ∧ banks.isEmpty do
      throw "Unexpected Deutsch–Jozsa oracle slot or wire forwarding"
    return .query
  | _ => throw "Unsupported instruction in the open Deutsch–Jozsa fragment"

/-- Interpret the supported instructions on the input/answer basis after resolving the RIR. -/
noncomputable def openCircuit (width : Nat) (program : Program) :
    Except String (Circuit (Reg width × Bool)) := do
  let resolved ← program.resolve
  unless resolved.wireCount = width + 1 do throw "Wrong Deutsch–Jozsa entry width"
  resolved.instructions.mapM (toStep width)

/-- The standard DJ circuit including initialization of the answer from zero. -/
@[expose] noncomputable def preparedCircuit (width : Nat) : Circuit (Reg width × Bool) :=
  [.gate (TensorGate 1 PauliX), .gate (TensorGate 1 Hadamard)] ++ djCircuit width

theorem resolve_generate (width : Nat) (positive : 0 < width) :
    (generate width).resolve = .ok (resolvedDJ width [query width]) := by
  have hWires : (List.range width ++ [width]).Nodup := by
    rw [← List.range_succ]
    exact List.nodup_range
  have hTake : (List.range width).take width = List.range width := by
    simpa only [List.length_range] using (List.take_length (l := List.range width))
  simp [generate, Program.resolve, checkInterface, lookupModule, List.lookup, bitsRef, resolvedDJ, query,
    positive, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [resolveModule.eq_2]
  dsimp only
  simp [resolveInstruction, lookupModule, rootRegisters, resolveRef, resolveCall,
    resolveBlock_root, RIR.lookup, List.lookup, ResolveContext.emit, ResolveContext.checkProtected,
    checkCapability, hWires, hTake, List.nodup_range,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [resolveModule.eq_2]
  rfl

theorem openCircuit_of_resolved (width : Nat) (program : Program)
    (resolved : program.resolve = .ok (resolvedDJ width [query width])) :
    openCircuit width program = .ok (preparedCircuit width) := by
  have hRange : List.range width ≠ [width] := by
    intro h
    have hw : width ∈ List.range width := by simp [h]
    simp at hw
  simp! [openCircuit, resolved, resolvedDJ, query, toStep, preparedCircuit, djCircuit, hRange,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The open RIR implements exact DJ under the standard XOR oracle interpretation. -/
@[expose] def Correct (width : Nat) (program : Program) : Prop :=
  ∃ circuit, openCircuit width program = .ok circuit ∧ QueryCount circuit = 1 ∧
    ∀ f : Reg width → Bool,
      Run (BitOracleOn f) circuit (TensorState (Ket (ZeroStr width)) (Ket false)) =
        TensorState (djFinalState f) Minus ∧
      (DJConstant f → MeasureProb (djFinalState f) ({ZeroStr width} : Finset (Reg width)) = 1) ∧
      (DJBalanced f →
        MeasureProb (djFinalState f) (Finset.univ.erase (ZeroStr width)) = 1)

/-- Any program resolving to the standard open word has the promised output rule. -/
theorem correct_of_resolved (width : Nat) (program : Program)
    (resolved : program.resolve = .ok (resolvedDJ width [query width])) : Correct width program := by
  refine ⟨preparedCircuit width, openCircuit_of_resolved width program resolved, ?_, ?_⟩
  · simp [preparedCircuit, djCircuit, QueryCount]
  · intro f
    refine ⟨?_, (deutschJozsa_single_query f).1, fun h => ((deutschJozsa_single_query f).2.1 h).2⟩
    change Run (BitOracleOn f) (djCircuit width)
      (ApplyGate (TensorGate 1 Hadamard)
        (ApplyGate (TensorGate 1 PauliX) (TensorState (Ket (ZeroStr width)) (Ket false)))) = _
    rw [applyGate_tensorGate, applyGate_one, applyGate_pauliX_ket]
    simp only [applyGate_tensorGate, applyGate_one, Bool.not_false, applyGate_hadamard_ket_true]
    exact (dj_circuit_run f).1

/-- The executable generator satisfies the DJ promise and uses one query at every positive width. -/
theorem generate_correct (width : Nat) (positive : 0 < width) : Correct width (generate width) :=
  correct_of_resolved width (generate width) (resolve_generate width positive)

/-- Check the public input/answer layout and the advertised readout register. -/
def checkEntry (width : Nat) (program : Program) : Except String Unit := do
  let entry ← lookupModule program program.entry
  unless entry.registers = [⟨"input", ⟨.bits, width⟩⟩, ⟨"answer", ⟨.bits, 1⟩⟩] do
    throw "Expected the Deutsch–Jozsa input and answer registers in that order"
  match entry.attributes.lookup "readout_register" with
  | some (.str "input") => return ()
  | _ => throw "Expected Deutsch–Jozsa readout from the input register"

/-- A checked open program has the standard trace and the same specification as the generator. -/
structure OpenCertificate (width : Nat) (program : Program) : Type where
  resolved : program.resolve = .ok (resolvedDJ width [query width])
  correct : Correct width program

/-- Check a serialized program's AST and return its exact resolved trace with the Lean proof. -/
def verifyOpen (width : Nat) (program : Program) : Except String (OpenCertificate width program) := do
  checkEntry width program
  let slot ← lookupModule program "dj_function"
  match slot.attributes.lookup "oracle_paradigm" with
  | some (.str "database_xor") => pure ()
  | _ => throw "Expected the database_xor oracle contract"
  match h : program.resolve with
  | .error reason => throw reason
  | .ok trace =>
    if ht : trace = resolvedDJ width [query width] then
      have resolved : program.resolve = .ok (resolvedDJ width [query width]) := ht ▸ h
      return ⟨resolved, correct_of_resolved width program resolved⟩
    else throw "Unexpected Deutsch–Jozsa instruction order or oracle forwarding"

end OracqVerify.Generators.DeutschJozsa
