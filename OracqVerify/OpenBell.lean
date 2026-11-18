module

public meta import Lean.Data.Json
public meta import Lean.Elab.Term

/-! Verification of the serialized two-wire Open Bell pilot. -/

public section

namespace OracqVerify.OpenBell

open Lean

inductive Gate where
  | h (wire : Fin 2)
  | cx (control target : Fin 2)
  deriving DecidableEq

meta section

private def expect (ok : Bool) (reason : String) : Except String Unit :=
  if ok then .ok () else .error reason

private def bits (width : Nat) : Json :=
  Json.mkObj [("kind", toJson "bits"), ("tag", toJson "RegType"), ("width", toJson width)]

private def ref (start width : Nat) : Json :=
  Json.mkObj [
    ("parts", .arr #[Json.mkObj [
      ("register", toJson "pair"), ("start", toJson start),
      ("tag", toJson "Span"), ("width", toJson width)]]),
    ("tag", toJson "Ref"), ("type", bits width)]

private def readWire (json : Json) : Except String (Fin 2) := do
  let part ← (← json.getObjVal? "parts").getArrVal? 0
  let start ← part.getObjValAs? Nat "start"
  expect (json == ref start 1) "Expected a single-bit pair span"
  if h : start < 2 then pure ⟨start, h⟩ else throw "Wire outside pair"

private def readGate (json : Json) : Except String Gate := do
  let op ← json.getObjValAs? String "op"
  let operands ← (← json.getObjVal? "operands").getArr?
  expect (json == Json.mkObj [
    ("angle", .null), ("op", toJson op), ("operands", .arr operands),
    ("tag", toJson "Primitive"), ("value", .null)]) "Expected a parameter-free primitive"
  match op, operands.toList with
  | "h", [wire] => return .h (← readWire wire)
  | "xor", [source, destination] =>
    let control ← readWire source
    let target ← readWire destination
    expect (control != target) "XOR aliases its control and target"
    return .cx control target
  | _, _ => throw "Unsupported primitive or arity"

private def call (callee : String) : Json :=
  Json.mkObj [
    ("arguments", .arr #[ref 0 2]), ("module", toJson callee),
    ("resources", .arr #[]), ("tag", toJson "Call")]

private def modules (text : String) : Except String (List Json) := do
  let json ← Json.parse text
  let definitions ← json.getObjVal? "modules"
  expect (json == Json.mkObj [
    ("entry", toJson "open_bell"), ("modules", definitions),
    ("tag", toJson "Program"), ("version", toJson "0.1")]) "Unsupported program"
  return (← definitions.getArr?).toList

private def readBody (json : Json) (name : String) : Except String Json := do
  let attrs ← json.getObjVal? "attributes"
  let body ← json.getObjVal? "body"
  let register := Json.mkObj [
    ("name", toJson "pair"), ("tag", toJson "Register"), ("type", bits 2)]
  expect (json == Json.mkObj [
    ("attributes", attrs), ("body", body), ("locals", .arr #[]), ("name", toJson name),
    ("registers", .arr #[register]), ("resources", .arr #[]), ("tag", toJson "Module")])
    s!"Unexpected module interface for {name}"
  return body

/-- Check the open and bound RIR together and inline the two whole-register calls. -/
def readBound (openRir boundRir : String) : Except String (List Gate) := do
  let [slot, entry] ← modules openRir | throw "Expected the open module table"
  let [boundSlot, impl, boundEntry] ← modules boundRir | throw "Expected the bound module table"
  expect ((← readBody slot "entangle") == .null) "Expected an open entangle slot"
  let entryBody ← readBody entry "open_bell"
  expect (boundEntry == entry) "Binding changed the entry module"
  let [first, invocation] := (← entryBody.getArr?).toList
    | throw "Expected a primitive followed by one call"
  expect (invocation == call "entangle") "Unexpected slot arguments"
  expect ((← readBody boundSlot "entangle") == .arr #[call "entangle_impl"])
    "Bound slot did not forward its full register"
  let implementation ← (← readBody impl "entangle_impl").getArr?
  return (← readGate first) :: (← implementation.toList.mapM readGate)

end

/-- Coefficients are scaled by `sqrt(2)^hadamards` to keep the interpreter exact. -/
structure State where
  amplitudes : Fin 4 → Int
  hadamards : Nat

/-- The computational basis state with both wires zero. -/
def zeroState : State :=
  ⟨fun index => if index = 0 then 1 else 0, 0⟩

private def toggle (index : Fin 4) (wire : Fin 2) : Fin 4 :=
  ⟨(index.val ^^^ (1 <<< wire.val)) % 4, Nat.mod_lt _ (by decide)⟩

/-- Apply a real Hadamard or controlled-X in little-endian basis order. -/
def step (state : State) (gate : Gate) : State :=
  match gate with
  | .h wire =>
    ⟨fun index =>
      let a := state.amplitudes index
      let b := state.amplitudes (toggle index wire)
      if index.val.testBit wire.val then b - a else a + b, state.hadamards + 1⟩
  | .cx control target =>
    ⟨fun index =>
      state.amplitudes (if index.val.testBit control.val then toggle index target else index),
      state.hadamards⟩

/-- Evaluate the gate word on the computational zero state. -/
def run (gates : List Gate) : State :=
  gates.foldl step zeroState

structure StrictCounts where
  h : Nat
  cz : Nat
  deriving DecidableEq

/-- Count the strict basis, in which controlled-X lowers to H, CZ, H on the target. -/
def strictCounts (gates : List Gate) : StrictCounts :=
  gates.foldl (fun counts gate => match gate with
    | .h _ => { counts with h := counts.h + 1 }
    | .cx _ _ => ⟨counts.h + 2, counts.cz + 1⟩) ⟨0, 0⟩

private meta instance : ToExpr Gate where
  toExpr
    | .h wire => mkApp (mkConst ``Gate.h) (toExpr wire)
    | .cx control target => mkApp2 (mkConst ``Gate.cx) (toExpr control) (toExpr target)
  toTypeExpr := mkConst ``Gate

local elab "decodeBellFixtures" : term =>
  match readBound
      (include_str "../fixtures/open_bell.open.json")
      (include_str "../fixtures/open_bell.bound.json") with
  | .ok gates => pure (toExpr gates)
  | .error reason => throwError "Invalid open_bell RIR: {reason}"

/-- The gate word decoded from the open and bound Oracq fixtures during elaboration. -/
def exportedProgram : List Gate := decodeBellFixtures

/-- The supplied open and bound Oracq artifacts decode to the Bell gate word. -/
theorem exported_program : exportedProgram = [.h 0, .cx 0 1] := by decide

/-- The decoded program produces `(1, 0, 0, 1) / sqrt(2)` from the zero state. -/
theorem exported_bell :
    (List.ofFn (run exportedProgram).amplitudes, (run exportedProgram).hadamards) =
      ([1, 0, 0, 1], 1) := by decide

private meta def readLedger (text : String) : Except String (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let json ← Json.parse text
  let atoms ← json.getObjVal? "atoms"
  return (← json.getObjValAs? Nat "qubits", ← atoms.getObjValAs? Nat "h",
    ← atoms.getObjValAs? Nat "cz", ← json.getObjValAs? Nat "gate_total",
    ← json.getObjValAs? Nat "qram_total", ← json.getObjValAs? Nat "t_total")

local elab "decodeBellLedger" : term =>
  match readLedger (include_str "../fixtures/open_bell.resources.json") with
  | .ok counts => pure (toExpr counts)
  | .error reason => throwError "Invalid open_bell resource ledger: {reason}"

/-- Frozen resource fields projected from the exported Bell ledger. -/
def ledger : Nat × Nat × Nat × Nat × Nat × Nat := decodeBellLedger

/-- The strict gate counts of the decoded RIR agree with the exported resource ledger. -/
theorem exported_counts :
    (let counts := strictCounts exportedProgram
     (2, counts.h, counts.cz, counts.h + counts.cz, 0, 0)) = ledger := by decide

end OracqVerify.OpenBell
