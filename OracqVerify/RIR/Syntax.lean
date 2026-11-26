module

public import Lean.Data.Json

/-! Executable syntax and the Oracq RIR 0.1 JSON encoding for the supported fragment. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

open Lean

variable {α : Type}

inductive RegKind where
  | bits | uint | sint | rational
  deriving DecidableEq, Repr

structure RegType where
  kind : RegKind
  width : Nat
  deriving DecidableEq, Repr

structure Register where
  name : String
  type : RegType
  deriving DecidableEq, Repr

structure Span where
  register : String
  start : Nat
  width : Nat
  deriving DecidableEq, Repr

structure Ref where
  type : RegType
  parts : List Span
  deriving DecidableEq, Repr

structure BankType where
  addressWidth : Nat
  dataWidth : Nat
  deriving DecidableEq, Repr

structure Resource where
  name : String
  type : BankType
  deriving DecidableEq, Repr

inductive UnaryGate where
  | h | x | z
  | ry (angle : JsonNumber)
  deriving DecidableEq, Repr

inductive Instruction where
  | unary (gate : UnaryGate) (target : Ref)
  | phase (angle : JsonNumber) (target : Ref)
  | gphase (angle : JsonNumber)
  | xor (source target : Ref)
  | swap (first second : Ref)
  | addConst (target : Ref) (amount : Nat)
  | load (resource : String) (address data : Ref)
  | call (moduleName : String) (arguments : List Ref) (resources : List String)
  | control (register : Ref) (value : Nat) (body : List Instruction)
  | adjoint (body : List Instruction)
  | repeat (count : Nat) (body : List Instruction)

structure Module where
  name : String
  registers : List Register
  resources : List Resource
  body : Option (List Instruction)
  attributes : List (String × Json) := []
  locals : List Register := []

structure Program where
  entry : String
  modules : List Module

/-- Construct a whole-register bit view. -/
@[expose] def bitsRef (name : String) (width : Nat) : Ref :=
  ⟨⟨.bits, width⟩, [⟨name, 0, width⟩]⟩

private def kindName : RegKind → String
  | .bits => "bits"
  | .uint => "uint"
  | .sint => "sint"
  | .rational => "rational"

def gateName : UnaryGate → String
  | .h => "h"
  | .x => "x"
  | .z => "z"
  | .ry _ => "ry"

def gateAngle : UnaryGate → Json
  | .ry angle => .num angle
  | _ => .null

private def object (tag : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("tag", toJson tag) :: fields)

private def arrays (encode : α → Json) (items : List α) : Json :=
  .arr (items.toArray.map encode)

private def encodeType (type : RegType) : Json :=
  object "RegType" [("kind", toJson (kindName type.kind)), ("width", toJson type.width)]

private def encodeRegister (register : Register) : Json :=
  object "Register" [("name", toJson register.name), ("type", encodeType register.type)]

private def encodeSpan (span : Span) : Json :=
  object "Span" [("register", toJson span.register), ("start", toJson span.start),
    ("width", toJson span.width)]

private def encodeRef (ref : Ref) : Json :=
  object "Ref" [("type", encodeType ref.type), ("parts", arrays encodeSpan ref.parts)]

private def encodeResource (resource : Resource) : Json :=
  object "Resource" [("name", toJson resource.name), ("type", object "QRAM"
    [("address_width", toJson resource.type.addressWidth),
     ("data_width", toJson resource.type.dataWidth)])]

private def primitive (op : String) (operands : List Ref) (angle : Json := .null)
    (value : Json := .null) : Json :=
  object "Primitive" [("op", toJson op), ("operands", arrays encodeRef operands),
    ("angle", angle), ("value", value)]

private def encodeInstruction : Instruction → Json
  | .unary g ref => primitive (gateName g) [ref] (gateAngle g)
  | .phase angle ref => primitive "phase" [ref] (.num angle)
  | .gphase angle => primitive "gphase" [] (.num angle)
  | .xor source target => primitive "xor" [source, target]
  | .swap first second => primitive "swap" [first, second]
  | .addConst target amount => primitive "add_const" [target] .null (toJson amount)
  | .load resource address data => object "Load"
      [("resource", toJson resource), ("address", encodeRef address), ("data", encodeRef data)]
  | .call target args resources => object "Call"
      [("module", toJson target), ("arguments", arrays encodeRef args),
       ("resources", toJson resources)]
  | .control register value body =>
    object "Control" [("register", encodeRef register), ("value", toJson value),
      ("body", arrays (fun node : { i // i ∈ body } => encodeInstruction node.val) body.attach)]
  | .adjoint body =>
    object "Adjoint"
      [("body", arrays (fun node : { i // i ∈ body } => encodeInstruction node.val) body.attach)]
  | .repeat count body =>
    object "Repeat" [("count", toJson count),
      ("body", arrays (fun node : { i // i ∈ body } => encodeInstruction node.val) body.attach)]
termination_by i => sizeOf i
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem node.property
    simp_wf
    omega

private def encodeModule (m : Module) : Json :=
  object "Module" [("name", toJson m.name), ("registers", arrays encodeRegister m.registers),
    ("resources", arrays encodeResource m.resources),
    ("body", (m.body.map (arrays encodeInstruction)).getD .null), ("locals", arrays encodeRegister m.locals),
    ("attributes", arrays (fun (key, value) => .arr #[toJson key, value]) m.attributes)]

/-- Serialize this AST as Oracq RIR 0.1. -/
def Program.toJson (p : Program) : Json :=
  object "Program" [("version", Lean.toJson "0.1"), ("entry", Lean.toJson p.entry),
    ("modules", arrays encodeModule p.modules)]

private def tag (j : Json) : Except String String :=
  j.getObjValAs? String "tag"

private def tagged (expected : String) (j : Json) : Except String Unit := do
  let actual ← tag j
  unless actual == expected do throw s!"Expected {expected}, got {actual}"

private def readList (decode : Json → Except String α) (j : Json) (field : String) :
    Except String (List α) := do
  let values ← (← j.getObjVal? field).getArr?
  values.toList.mapM decode

private def decodeType (j : Json) : Except String RegType := do
  tagged "RegType" j
  let kind ← match ← j.getObjValAs? String "kind" with
    | "bits" => pure RegKind.bits
    | "uint" => pure RegKind.uint
    | "sint" => pure RegKind.sint
    | "rational" => pure RegKind.rational
    | k => throw s!"Unsupported register kind: {k}"
  return ⟨kind, ← j.getObjValAs? Nat "width"⟩

private def decodeRegister (j : Json) : Except String Register := do
  tagged "Register" j
  return ⟨← j.getObjValAs? String "name", ← decodeType (← j.getObjVal? "type")⟩

private def decodeSpan (j : Json) : Except String Span := do
  tagged "Span" j
  return ⟨← j.getObjValAs? String "register", ← j.getObjValAs? Nat "start",
    ← j.getObjValAs? Nat "width"⟩

private def decodeRef (j : Json) : Except String Ref := do
  tagged "Ref" j
  return ⟨← decodeType (← j.getObjVal? "type"), ← readList decodeSpan j "parts"⟩

private def decodeResource (j : Json) : Except String Resource := do
  tagged "Resource" j
  let ty ← j.getObjVal? "type"
  tagged "QRAM" ty
  return ⟨← j.getObjValAs? String "name",
    ⟨← ty.getObjValAs? Nat "address_width", ← ty.getObjValAs? Nat "data_width"⟩⟩

private def decodeInstruction : Nat → Json → Except String Instruction
  | 0, _ => .error "RIR block nesting exceeds 127"
  | fuel + 1, j => do
    match ← tag j with
    | "Primitive" =>
      let angle ← j.getObjVal? "angle"
      let value ← j.getObjVal? "value"
      match ← j.getObjValAs? String "op", ← readList decodeRef j "operands", angle, value with
      | "h", [arg], .null, .null => return .unary .h arg
      | "x", [arg], .null, .null => return .unary .x arg
      | "z", [arg], .null, .null => return .unary .z arg
      | "ry", [arg], .num θ, .null => return .unary (.ry θ) arg
      | "phase", [arg], .num θ, .null => return .phase θ arg
      | "gphase", [], .num θ, .null => return .gphase θ
      | "xor", [src, dst], .null, .null => return .xor src dst
      | "swap", [first, second], .null, .null => return .swap first second
      | "add_const", [target], .null, .num _ => return .addConst target (← value.getNat?)
      | op, _, _, _ => throw s!"Unsupported primitive or parameters: {op}"
    | "Load" =>
      return .load (← j.getObjValAs? String "resource") (← decodeRef (← j.getObjVal? "address"))
        (← decodeRef (← j.getObjVal? "data"))
    | "Call" =>
      return .call (← j.getObjValAs? String "module") (← readList decodeRef j "arguments")
        (← j.getObjValAs? (List String) "resources")
    | "Control" =>
      return .control (← decodeRef (← j.getObjVal? "register")) (← j.getObjValAs? Nat "value")
        (← readList (decodeInstruction fuel) j "body")
    | "Adjoint" =>
      return .adjoint (← readList (decodeInstruction fuel) j "body")
    | "Repeat" =>
      return .repeat (← j.getObjValAs? Nat "count") (← readList (decodeInstruction fuel) j "body")
    | kind => throw s!"Unsupported RIR instruction: {kind}"

private def decodeAttr (j : Json) : Except String (String × Json) := do
  let #[key, value] ← j.getArr? | throw "Expected an attribute pair"
  return (← key.getStr?, value)

private def decodeModule (j : Json) : Except String Module := do
  tagged "Module" j
  let body ← match ← j.getObjVal? "body" with
    | .null => pure none
    | .arr xs => some <$> xs.toList.mapM (decodeInstruction 128)
    | _ => throw "Expected a module body or an open declaration"
  return ⟨← j.getObjValAs? String "name", ← readList decodeRegister j "registers",
    ← readList decodeResource j "resources", body, ← readList decodeAttr j "attributes",
    ← readList decodeRegister j "locals"⟩

/-- Decode the supported syntax. Use the resolver to check cross-module constraints. -/
def Program.fromJson (j : Json) : Except String Program := do
  tagged "Program" j
  unless (← j.getObjValAs? String "version") == "0.1" do throw "Unsupported RIR version"
  return ⟨← j.getObjValAs? String "entry", ← readList decodeModule j "modules"⟩

end OracqVerify.RIR
