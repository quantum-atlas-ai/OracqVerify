module

public import OracqVerify.Verification.Oracle

/-! Check that concrete DJ bindings realize the open oracle boundary and its output promise. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.DeutschJozsa

open Lean OracqVerify.RIR
open OracqVerify.Generators.DeutschJozsa
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

inductive Implementation (width : Nat) where
  | constant (bit : Bool)
  | inputBit (wire : Fin width)
  | qram (bankName : String) (table : DenseTable width)

def Implementation.value {width : Nat} (impl : Implementation width) : Reg width → Bool :=
  match impl with
  | .constant b => fun _ => b
  | .inputBit i => fun address => address i
  | .qram _ t => t.value

def Implementation.instructions {width : Nat} (impl : Implementation width) :
    List ResolvedInstruction :=
  match impl with
  | .constant false => []
  | .constant true => [.unary .x [width]]
  | .inputBit i => [.xor [i.val] [width]]
  | .qram name _ => [.load ⟨name, ⟨width, 1⟩⟩ (List.range width) [width]]

/-- A QRAM implementation uses the words decoded from the actual supplied snapshot. -/
def Implementation.MatchesSnapshot {width : Nat} (impl : Implementation width)
    (snapshot : Json) : Prop :=
  match impl with
  | .qram name table => DenseTable.decode width name snapshot = .ok table
  | _ => True

def Implementation.checkPromise {width : Nat} (impl : Implementation width) :
    Except String {kind : Promise // kind.Holds impl.value} :=
  match impl with
  | .constant b => .ok ⟨.constant, ⟨b, fun _ => rfl⟩⟩
  | .inputBit i => .ok ⟨.balanced, inputBit_balanced i⟩
  | .qram _ t => t.checkPromise

/-- Interpret the supported binding instructions in the resolved input/answer layout. -/
noncomputable def Implementation.circuit {width : Nat} (impl : Implementation width) :
    Circuit (Reg width × Bool) :=
  match impl with
  | .constant false => []
  | .constant true => [.gate (TensorGate 1 PauliX)]
  | .inputBit i => [.gate (BitOracleOn (fun address => address i))]
  | .qram _ t => [.gate (tableMatrix t)]

theorem Implementation.run_circuit {width : Nat} (impl : Implementation width)
    (state : QState (Reg width × Bool)) :
    Run (BitOracleOn impl.value) impl.circuit state = ApplyGate (BitOracleOn impl.value) state := by
  cases impl with
  | constant b =>
    cases b
    · simp [Implementation.circuit, Implementation.value, zeroOracle, applyGate_one]
    · simp [Implementation.circuit, Implementation.value, oneOracle]
  | inputBit i => simp [Implementation.circuit, Implementation.value]
  | qram name table => simp [Implementation.circuit, Implementation.value, tableMatrix_spec]

/-- The independent closed word uses the actual binding's gates in place of the query. -/
noncomputable def closedWord {width : Nat} (impl : Implementation width) :
    Circuit (Reg width × Bool) :=
  [.gate (TensorGate 1 PauliX), .gate (TensorGate 1 Hadamard), .gate (LiftGate (HadamardN width))] ++
    impl.circuit ++ [.gate (LiftGate (HadamardN width))]

/-- At every input state, the supported concrete oracle can replace the logical call. -/
theorem run_closedWord {width : Nat} (impl : Implementation width)
    (state : QState (Reg width × Bool)) :
    Run (BitOracleOn impl.value) (closedWord impl) state =
      Run (BitOracleOn impl.value) (preparedCircuit width) state := by
  simp [closedWord, preparedCircuit, djCircuit, run_append, impl.run_circuit]

/-- The closed resolver identifies the actual instruction sequence interpreted by closedWord. -/
noncomputable def boundCircuit {width : Nat} (program : Program) (impl : Implementation width) :
    Except String (Circuit (Reg width × Bool)) :=
  match program.resolve with
  | .error reason => .error reason
  | .ok trace =>
    if trace = resolvedDJ width impl.instructions then .ok (closedWord impl)
    else .error "Unexpected closed Deutsch–Jozsa trace"

/-- Hide only the selected wrapper implementation while retaining all forwarded bank formals. -/
def atOracleBoundary (program : Program) : Program :=
  { program with modules := program.modules.map fun m =>
    if m.name == "dj_function" then { m with body := none } else m }

private def readBoundary (width : Nat) (trace : ResolvedProgram) :
    Except String {banks : List Resource // trace = resolvedDJ width [query width banks]} := do
  let [_, _, _, .query _ _ banks, _] := trace.instructions |
    throw "Expected exactly one call at the Deutsch–Jozsa oracle boundary"
  if h : trace = resolvedDJ width [query width banks] then return ⟨banks, h⟩
  else throw "The binding changed the Deutsch–Jozsa instruction order or oracle forwarding"

private def checkWrapper (width : Nat) (slot : RIR.Module) : Except String Unit := do
  let some [.call _ arguments _] := slot.body |
    throw "Expected a bound Deutsch–Jozsa wrapper with one implementation call"
  unless arguments = [bitsRef "address" width, bitsRef "data" 1] do
    throw "The bound wrapper must forward the complete address and answer in signature order"

private def readImplementation (width : Nat) (banks : List Resource)
    (instructions : List ResolvedInstruction) (snapshot : Json) :
    Except String {impl : Implementation width // impl.MatchesSnapshot snapshot} := do
  match banks, instructions with
  | [], [] => return ⟨.constant false, trivial⟩
  | [], [.unary .x [target]] =>
    unless target = width do throw "The constant oracle must only flip the answer wire"
    return ⟨.constant true, trivial⟩
  | [], [.xor [source] [target]] =>
    unless target = width do throw "The bit oracle must XOR into the answer wire"
    if h : source < width then return ⟨.inputBit ⟨source, h⟩, trivial⟩
    else throw "The bit oracle must read an input wire"
  | [bank], [.load actual address data] =>
    unless actual = bank ∧ bank.type = ⟨width, 1⟩ do
      throw "The QRAM read must use the forwarded one-bit bank"
    unless address = List.range width ∧ data = [width] do
      throw "The QRAM oracle must read the complete input in order and XOR into the answer"
    match decoded : DenseTable.decode width bank.name snapshot with
    | .error reason => throw reason
    | .ok table => return ⟨.qram bank.name table, decoded⟩
  | _, _ => throw "Unsupported oracle implementation at the Deutsch–Jozsa boundary"

/-- A certificate records the open trace, the closed trace, and the concrete oracle promise. -/
structure BoundCertificate (width : Nat) (original bound : Program) (snapshot : Json) where
  implementation : Implementation width
  matches_snapshot : implementation.MatchesSnapshot snapshot
  promise : Promise
  promise_holds : promise.Holds implementation.value
  open_resolved : original.resolve = .ok (resolvedDJ width [query width])
  banks : List Resource
  boundary_resolved : (atOracleBoundary bound).resolve = .ok (resolvedDJ width [query width banks])
  closed_resolved : bound.resolve = .ok (resolvedDJ width implementation.instructions)

/-- Check an open/bound artifact pair and the actual dense memory used by a QRAM binding. -/
def verifyBound (width : Nat) (original bound : Program) (snapshot : Json) :
    Except String (BoundCertificate width original bound snapshot) := do
  let openEvidence ← verifyOpen width original
  checkEntry width bound
  unless original.entry = bound.entry do throw "The binding changed the entry module"
  let slot ← lookupModule bound "dj_function"
  checkWrapper width slot
  match hBoundary : (atOracleBoundary bound).resolve with
  | .error reason => throw reason
  | .ok boundary =>
    let banks ← readBoundary width boundary
    match hClose : bound.resolve with
    | .error reason => throw reason
    | .ok trace =>
      let impl ← readImplementation width banks.val (trace.instructions.drop 3).dropLast snapshot
      let promise ← impl.val.checkPromise
      if hTrace : trace = resolvedDJ width impl.val.instructions then
        return ⟨impl.val, impl.property, promise.val, promise.property, openEvidence.resolved, banks.val,
          banks.property ▸ hBoundary, hTrace ▸ hClose⟩
      else throw "Unexpected closed Deutsch–Jozsa trace"

/-- The closed RIR and the independently checked open RIR have equal execution for every state. -/
theorem BoundCertificate.link {width : Nat} {original bound : Program} {snapshot : Json}
    (evidence : BoundCertificate width original bound snapshot) :
    ∃ closedWord openWord,
      boundCircuit bound evidence.implementation = .ok closedWord ∧
      openCircuit width original = .ok openWord ∧
      ∀ state,
        Run (BitOracleOn evidence.implementation.value) closedWord state =
        Run (BitOracleOn evidence.implementation.value) openWord state := by
  refine ⟨closedWord evidence.implementation, preparedCircuit width, ?_,
    openCircuit_of_resolved width original evidence.open_resolved, run_closedWord _⟩
  simp [boundCircuit, evidence.closed_resolved]

/-- A checked binding inherits the open theorem on initialization, readout, and query budget. -/
theorem BoundCertificate.correct {width : Nat} {original bound : Program} {snapshot : Json}
    (evidence : BoundCertificate width original bound snapshot) :
    ∃ circuit,
      boundCircuit bound evidence.implementation = .ok circuit ∧
      Run (BitOracleOn evidence.implementation.value) circuit
          (TensorState (Ket (ZeroStr width)) (Ket false)) =
        TensorState (djFinalState evidence.implementation.value) Minus ∧
      (match evidence.promise with
      | .constant =>
        MeasureProb (djFinalState evidence.implementation.value) ({ZeroStr width} : Finset _) = 1
      | .balanced =>
        MeasureProb (djFinalState evidence.implementation.value) (Finset.univ.erase (ZeroStr width)) = 1) ∧
      QueryCount (preparedCircuit width) = 1 := by
  obtain ⟨openWord, hop, hcount, hcorrect⟩ :=
    correct_of_resolved width original evidence.open_resolved
  have heq : openWord = preparedCircuit width :=
    Except.ok.inj (hop.symm.trans (openCircuit_of_resolved width original evidence.open_resolved))
  subst openWord
  obtain ⟨hstate, hconstant, hbalanced⟩ := hcorrect evidence.implementation.value
  refine ⟨closedWord evidence.implementation, ?_, ?_, ?_, hcount⟩
  · simp [boundCircuit, evidence.closed_resolved]
  · rw [run_closedWord, hstate]
  · have hp := evidence.promise_holds
    cases hk : evidence.promise
    · exact hconstant (by simpa [hk, Promise.Holds] using hp)
    · exact hbalanced (by simpa [hk, Promise.Holds] using hp)

/-- Resource units for this exact, rotation-free fragment. -/
structure Ledger where
  qubits : Nat
  h : Nat := 0
  x : Nat := 0
  cz : Nat := 0
  qram : Nat := 0
  deriving Repr, DecidableEq

/-- Fold the closed trace using Oracq's H–CZ–H expansion of a bitwise XOR. -/
def countTrace (trace : ResolvedProgram) : Except String Ledger :=
  trace.instructions.foldlM (fun ledger step =>
    match step with
    | .unary .h wires => .ok { ledger with h := ledger.h + wires.length }
    | .unary .x wires => .ok { ledger with x := ledger.x + wires.length }
    | .xor source _ =>
      .ok { ledger with
        h := ledger.h + 2 * source.length
        cz := ledger.cz + source.length }
    | .load .. => .ok { ledger with qram := ledger.qram + 1 }
    | _ => .error "The strict DJ ledger requires a supported closed instruction")
    { qubits := trace.wireCount }

/-- The ledger counts the exact closed trace preserved by the certificate. -/
def BoundCertificate.ledger {width : Nat} {original bound : Program} {snapshot : Json}
    (evidence : BoundCertificate width original bound snapshot) : Except String Ledger :=
  countTrace (resolvedDJ width evidence.implementation.instructions)

theorem BoundCertificate.ledger_eq {width : Nat} {original bound : Program} {snapshot : Json}
    (evidence : BoundCertificate width original bound snapshot) :
    bound.resolve.bind countTrace = evidence.ledger := by
  rw [evidence.closed_resolved]
  rfl

end OracqVerify.Verification.DeutschJozsa
