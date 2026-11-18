import OracqVerify.OpenBell

/-! Verify the open Deutsch–Jozsa entry and two concrete Oracq gate bindings. -/

set_option warningAsError true

namespace OracqVerify.DeutschJozsa

open Lean

structure Program where
  width : Nat
  copiesFirstBit : Bool
  slotCalls : Nat
  deriving DecidableEq

private def require (ok : Bool) (reason : String) : Except String Unit :=
  if ok then .ok () else .error reason

private def bits (width : Nat) : Json :=
  Json.mkObj [("kind", toJson "bits"), ("tag", toJson "RegType"), ("width", toJson width)]

private def register (name : String) (width : Nat) : Json :=
  Json.mkObj [("name", toJson name), ("tag", toJson "Register"), ("type", bits width)]

private def ref (name : String) (width : Nat) : Json :=
  Json.mkObj [("parts", .arr #[Json.mkObj [
      ("register", toJson name), ("start", toJson (0 : Nat)),
      ("tag", toJson "Span"), ("width", toJson width)]]),
    ("tag", toJson "Ref"), ("type", bits width)]

private def primitive (op : String) (operands : Array Json) : Json :=
  Json.mkObj [("angle", .null), ("op", toJson op), ("operands", .arr operands),
    ("tag", toJson "Primitive"), ("value", .null)]

private def call (name : String) (args : Array Json) : Json :=
  Json.mkObj [("arguments", .arr args), ("module", toJson name),
    ("resources", .arr #[]), ("tag", toJson "Call")]

private def programModules (text : String) : Except String (String × List Json) := do
  let root ← Json.parse text
  let entry ← root.getObjValAs? String "entry"
  let modules ← root.getObjVal? "modules"
  require (root == Json.mkObj [("entry", toJson entry), ("modules", modules),
    ("tag", toJson "Program"), ("version", toJson "0.1")]) "Unsupported RIR program"
  return (entry, (← modules.getArr?).toList)

private def requireModule (j : Json) (name : String) (registers : Array Json)
    (body : Json) : Except String Unit := do
  let attributes ← j.getObjVal? "attributes"
  require (j == Json.mkObj [("attributes", attributes), ("body", body), ("locals", .arr #[]),
    ("name", toJson name), ("registers", .arr registers), ("resources", .arr #[]),
    ("tag", toJson "Module")]) s!"Unexpected module interface or body for {name}"

/-- Validate the preparation, one slot call, readout basis change, and bound oracle forwarding. -/
def readBound (openRir boundRir : String) : Except String Program := do
  let (entryName, [openEntry, openSlot]) ← programModules openRir
    | throw "Expected the Deutsch–Jozsa open module table"
  let (boundName, [implementation, boundEntry, boundSlot]) ← programModules boundRir
    | throw "Expected the Deutsch–Jozsa bound module table"
  require (entryName == boundName && openEntry == boundEntry) "Binding changed the entry"
  require ((← openEntry.getObjVal? "attributes") == toJson
    ([ ["algorithm", "deutsch_jozsa"], ["readout_register", "input"],
      ["validation_stage", "paradigm"] ] : List (List String))) "Expected readout on the input register"
  let input ← (← openEntry.getObjVal? "registers").getArrVal? 0
  let width ← (← input.getObjVal? "type").getObjValAs? Nat "width"
  require (width > 0) "The input register must be nonempty"
  let inputRef := ref "input" width
  let answer := ref "answer" 1
  let inputH := primitive "h" #[inputRef]
  requireModule openEntry entryName #[register "input" width, register "answer" 1] (.arr #[
    primitive "x" #[answer], primitive "h" #[answer], inputH,
    call "dj_function" #[inputRef, answer], inputH])
  let oracleRegisters := #[register "address" width, register "data" 1]
  requireModule openSlot "dj_function" oracleRegisters .null
  let implementationName ← implementation.getObjValAs? String "name"
  require (implementationName != entryName && implementationName != "dj_function")
    "Oracle implementation must name a distinct module"
  requireModule boundSlot "dj_function" oracleRegisters (.arr #[
    call implementationName #[ref "address" width, ref "data" 1]])
  let implementationBody ← implementation.getObjVal? "body"
  let copiesFirstBit := implementationBody == .arr #[primitive "xor" #[ref "address" 1, ref "data" 1]]
  require (copiesFirstBit || implementationBody == .arr #[])
    "Expected identity or a controlled flip from the first address bit"
  requireModule implementation implementationName oracleRegisters implementationBody
  let body ← (← openEntry.getObjVal? "body").getArr?
  let calls := body.filter (fun instr => (instr.getObjValAs? String "tag").toOption == some "Call")
  return ⟨width, copiesFirstBit, calls.size⟩

/-- Strict H count, including the two target H gates used to lower a controlled flip. -/
def hCount (program : Program) : Nat :=
  2 * program.width + 1 + if program.copiesFirstBit then 2 else 0

/-- Strict CZ count of the admitted oracle implementation. -/
def czCount (program : Program) : Nat := if program.copiesFirstBit then 1 else 0

private abbrev Ledger := Nat × Nat × Nat × Nat × Nat × Nat × Nat

private def receipt (program : Program) : Ledger :=
  (program.width + 1, hCount program, czCount program, 1,
    hCount program + czCount program + 1, 0, 0)

private def readLedger (text : String) : Except String Ledger := do
  let j ← Json.parse text
  require (← j.getObjValAs? Bool "complete") "Expected a complete resource ledger"
  let atoms ← j.getObjVal? "atoms"
  let h ← atoms.getObjValAs? Nat "h"
  let x ← atoms.getObjValAs? Nat "x"
  let cz ← match atoms.getObjVal? "cz" with
    | .ok value => fromJson? value
    | .error _ => pure 0
  let expected := [("h", toJson h), ("x", toJson x)]
  require (atoms == Json.mkObj (if cz = 0 then expected else ("cz", toJson cz) :: expected))
    "Expected exactly the supported strict atoms"
  return (← j.getObjValAs? Nat "qubits", h, cz, x, ← j.getObjValAs? Nat "gate_total",
    ← j.getObjValAs? Nat "qram_total", ← j.getObjValAs? Nat "t_total")

private abbrev Fixture := (Nat × Bool × Nat) × Ledger

private def readFixture (closed ledger : String) : Except String Fixture := do
  let p ← readBound (include_str "../fixtures/deutsch_jozsa.open.json") closed
  return ((p.width, p.copiesFirstBit, p.slotCalls), ← readLedger ledger)

local elab "decodeDjFixtures" : term =>
  match readFixture (include_str "../fixtures/deutsch_jozsa.constant.json")
          (include_str "../fixtures/deutsch_jozsa.constant.resources.json"),
        readFixture (include_str "../fixtures/deutsch_jozsa.balanced.json")
          (include_str "../fixtures/deutsch_jozsa.balanced.resources.json") with
  | .ok constant, .ok balanced => pure (toExpr (constant, balanced))
  | .error reason, _ => throwError "Invalid constant Deutsch–Jozsa fixture: {reason}"
  | _, .error reason => throwError "Invalid balanced Deutsch–Jozsa fixture: {reason}"

private def fixtures : Fixture × Fixture := decodeDjFixtures

/-- The one-bit program decoded from the open and constant-bound artifacts. -/
def constantProgram : Program := ⟨fixtures.1.1.1, fixtures.1.1.2.1, fixtures.1.1.2.2⟩

/-- The one-bit program decoded from the open and balanced-bound artifacts. -/
def balancedProgram : Program := ⟨fixtures.2.1.1, fixtures.2.1.2.1, fixtures.2.1.2.2⟩

/-- The admitted constant binding preserves the input and is counted as an empty oracle body. -/
theorem exported_constant_program : constantProgram = ⟨1, false, 1⟩ := by decide

/-- The admitted balanced binding conditionally flips the answer using the first input bit. -/
theorem exported_balanced_program : balancedProgram = ⟨1, true, 1⟩ := by decide

/-- Each entry makes one call at the declared oracle boundary. -/
theorem exported_slot_calls : constantProgram.slotCalls = 1 ∧ balancedProgram.slotCalls = 1 := by
  decide

/-- Both decoded programs count the same strict atoms as their own exported ledgers. -/
theorem exported_counts : receipt constantProgram = fixtures.1.2 ∧
    receipt balancedProgram = fixtures.2.2 := by
  constructor <;> decide

private def xAnswer (state : OpenBell.State) : OpenBell.State :=
  { state with amplitudes := fun i => state.amplitudes ⟨(i.val + 2) % 4, Nat.mod_lt _ (by decide)⟩ }

/-- Evaluate an admitted one-bit artifact on the zero state in little-endian basis order. -/
def runOneBit (program : Program) : Option OpenBell.State :=
  if program.width = 1 then
    let prepared := OpenBell.step (OpenBell.step (xAnswer OpenBell.zeroState) (.h 1)) (.h 0)
    let queried := if program.copiesFirstBit then OpenBell.step prepared (.cx 0 1) else prepared
    some (OpenBell.step queried (.h 0))
  else none

private def readAmplitudes (state : OpenBell.State) : List Int × Nat :=
  (List.ofFn state.amplitudes, state.hadamards)

/-- The actual constant and balanced exports have support on opposite input-bit values. -/
theorem exported_readout :
    (runOneBit constantProgram).map readAmplitudes = some ([2, 0, -2, 0], 3) ∧
    (runOneBit balancedProgram).map readAmplitudes = some ([0, 2, 0, -2], 3) := by decide

end OracqVerify.DeutschJozsa
