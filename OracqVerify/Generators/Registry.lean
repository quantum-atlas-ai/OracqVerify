module

public import OracqVerify.Verification.Bound
public import OracqVerify.Generators.Grover

/-! Registry of executable circuit generators and proofs about their returned RIR. -/

set_option warningAsError true

public section

namespace OracqVerify.Generators

open Lean OracqVerify.RIR

/-- A registered generator has executable parameters and a proof about every produced program. -/
structure CertifiedGenerator where
  theoremName : Name
  usage : String
  Parameters : Type
  parse : List String → Except String Parameters
  satisfies : Parameters → Program → Prop
  generate : (parameters : Parameters) → {program : Program // satisfies parameters program}
  check : (parameters : Parameters) → (program : Program) →
    Except String (Subtype fun _ : Unit => satisfies parameters program)
  checkBound : Parameters → Program → Program → Json → Except String Json

private def parsePositiveWidth (args : List String) : Except String {width : Nat // 0 < width} := do
  let [arg] := args | throw "Expected one argument: a positive address width"
  let some width := arg.toNat? | throw "Address width must be a positive integer"
  if h : 0 < width then return ⟨width, h⟩
  else throw "Address width must be a positive integer"

private def djBoundReport (width : Nat) (original bound : Program) (snapshot : Json) :
    Except String Json := do
  let evidence ← Verification.DeutschJozsa.verifyBound width original bound snapshot
  let (promise, readout) := match evidence.promise with
    | .constant => ("constant", "zero")
    | .balanced => ("balanced", "nonzero")
  let ledger ← evidence.ledger
  return Json.mkObj [
    ("verified", toJson true), ("mode", toJson "bound"), ("promise", toJson promise),
    ("readout", toJson readout), ("logical_oracle_calls", toJson (1 : Nat)),
    ("qram_banks", toJson (evidence.banks.map Resource.name)),
    ("resources", Json.mkObj [
      ("qubits", toJson ledger.qubits), ("h", toJson ledger.h), ("x", toJson ledger.x),
      ("cz", toJson ledger.cz), ("gate_total", toJson (ledger.h + ledger.x + ledger.cz)),
      ("qram_total", toJson ledger.qram)])]

private def deutschJozsa : CertifiedGenerator where
  theoremName := ``DeutschJozsa.generate_correct
  usage := "<address-width>"
  Parameters := {width : Nat // 0 < width}
  parse := parsePositiveWidth
  satisfies := fun width => DeutschJozsa.Correct width.val
  generate := fun width =>
    ⟨DeutschJozsa.generate width.val, DeutschJozsa.generate_correct width.val width.property⟩
  check := fun width program => do
    let evidence ← DeutschJozsa.verifyOpen width.val program
    return ⟨(), evidence.correct⟩
  checkBound := fun width => djBoundReport width.val

private def parseGroverAddress (args : List String) : Except String Grover.Address := do
  let [arg] := args | throw "Expected one argument: a marked address from 0 to 3"
  let some index := arg.toNat? | throw "Marked address must be an integer from 0 to 3"
  if h : index < 4 then return ⟨index, h⟩
  else throw "Marked address must be an integer from 0 to 3"

private def groverBoundReport (index : Grover.Address) (original bound : Program)
    (image : Json) : Except String Json := do
  let _ ← Grover.check index original
  let entry ← lookupModule bound bound.entry
  let implementation : Verification.Grover.Implementation :=
    if entry.resources.isEmpty then .gate else .qram
  let _ ← Verification.Grover.certifyAt original bound image implementation index
  return Json.mkObj [("verified", toJson true), ("mode", toJson "bound"),
    ("theorem", toJson (toString ``Grover.generate_correct)),
    ("implementation", toJson (if implementation.isQram then "qram" else "gate")),
    ("marked_address", toJson index.val), ("success_probability", toJson "1")]

private def grover : CertifiedGenerator where
  theoremName := ``Grover.generate_correct
  usage := "<marked-address>"
  Parameters := Grover.Address
  parse := parseGroverAddress
  satisfies := Grover.Correct
  generate := fun target => ⟨Grover.generate target, Grover.generate_correct target⟩
  check := Grover.check
  checkBound := groverBoundReport

/-- Each entry names the Lean theorem used by its proof-carrying generator. -/
def registry : List CertifiedGenerator := [deutschJozsa, grover]

private def withGenerator {α : Type} (theoremName : String)
    (use : CertifiedGenerator → Except String α) : Except String α := do
  let some generator := registry.find? (fun item => item.theoremName.toString == theoremName) |
    throw s!"Unknown generator theorem: {theoremName}. Use list to see registered theorems."
  use generator

/-- Dispatch using the fully qualified Lean theorem name. -/
def generate (theoremName : String) (args : List String) : Except String Program :=
  withGenerator theoremName fun generator => do
    let parameters ← generator.parse args
    return (generator.generate parameters).val

/-- Verify an open program under the registered logical contract. -/
def verify (theoremName : String) (args : List String) (program : Program) : Except String Json :=
  withGenerator theoremName fun generator => do
    let parameters ← generator.parse args
    let _ ← generator.check parameters program
    return Json.mkObj [("verified", toJson true), ("mode", toJson "open"),
      ("theorem", toJson theoremName)]

/-- Verify a binding and report the promised readout and the closed resource totals. -/
def verifyBound (theoremName : String) (args : List String) (original bound : Program)
    (snapshot : Json) : Except String Json :=
  withGenerator theoremName fun generator => do
    let parameters ← generator.parse args
    generator.checkBound parameters original bound snapshot

end OracqVerify.Generators
