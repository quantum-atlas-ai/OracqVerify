module

public import OracqVerify.RIR.SourceLink
public import OracqVerify.Verification.ReversibleFrame

/-! A decoder and checked semantics for modular OriginIR-ext exports in the supported gate fragment. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR.OriginIR

open Lean Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

def trimmed (s : String) : String := s.trimAscii.toString

def parseNat (s : String) : Except String Nat :=
  match (trimmed s).toNat? with
  | some value => .ok value
  | none => .error s!"Expected OriginIR integer: {s}"

def enclosed (text suffix : String) : Except String String := do
  unless text.endsWith suffix do throw s!"Missing {suffix} in OriginIR text"
  return (text.dropEnd suffix.length).toString

def splitArgs (body : String) : List String :=
  if (trimmed body).isEmpty then [] else (body.splitOn ",").map trimmed

def application (text : String) : Except String (String × List String) := do
  let [name, arguments] := text.splitOn "(" | throw "Expected OriginIR module application"
  return (trimmed name, splitArgs (← enclosed arguments ")"))

def indexed (text : String) : Except String (String × Nat) := do
  let [name, index] := text.splitOn "[" | throw s!"Expected indexed OriginIR wire: {text}"
  if name.isEmpty then throw "Empty OriginIR register name"
  return (name, ← parseNat (← enclosed index "]"))

def bankDecl (line : String) : Except String Resource := do
  let [name, dimensions] := (trimmed (line.drop 8).toString).splitOn " " |
    throw "Malformed QRAMDECL"
  unless name.startsWith "ram_" do throw "Unexpected exported bank name"
  let [address, data] := splitArgs dimensions | throw "Expected address and data widths"
  return ⟨(name.drop 4).toString, ⟨← parseNat address, ← parseNat data⟩⟩

def angle (token : String) : Except String JsonNumber := do
  unless token.startsWith "(" do throw "Expected a parenthesized OriginIR angle"
  match ← Json.parse (← enclosed ((token.drop 1).toString) ")") with
  | .num value => return value
  | _ => throw "Expected a decimal OriginIR angle"

def wire (registers : List Register) (token : String) : Except String Span := do
  let (name, bit) ← indexed token
  let some reg := registers.find? (fun r => r.name == name) | throw s!"Unknown target register {name}"
  unless bit < reg.type.width do throw "OriginIR wire is outside its register"
  return ⟨name, bit, 1⟩

def view (registers : List Register) (tokens : List String) : Except String Ref :=
  return ⟨⟨.bits, tokens.length⟩, ← tokens.mapM (wire registers)⟩

def quantumArguments (registers : List Register) :
    List Register → List String → Except String (List Ref)
  | [], [] => .ok []
  | [], _ :: _ => .error "Extra OriginIR module arguments"
  | r :: rest, tokens => do
    unless r.type.width ≤ tokens.length do throw "Missing OriginIR module arguments"
    return (← view registers (tokens.take r.type.width)) ::
      (← quantumArguments registers rest (tokens.drop r.type.width))

def atomic (registers : List Register) (banks : List Resource) (modules : List Module)
    (line : String) : Except String Instruction := do
  let opcode := (line.takeWhile (· != ' ')).toString
  let arguments := splitArgs (line.drop (opcode.length + 1)).toString
  match opcode, arguments with
  | "H", [target] => return .unary .h (← view registers [target])
  | "X", [target] => return .unary .x (← view registers [target])
  | "Z", [target] => return .unary .z (← view registers [target])
  | "RY", [target, value] => return .unary (.ry (← angle value)) (← view registers [target])
  | "U1", [target, value] => return .phase (← angle value) (← view registers [target])
  | "CNOT", [first, second] => return .xor (← view registers [first]) (← view registers [second])
  | "SWAP", [first, second] => return .swap (← view registers [first]) (← view registers [second])
  | _, _ =>
    if opcode.startsWith "ram_" then
      let name := (opcode.drop 4).toString
      let some bank := banks.find? (fun r => r.name == name) | throw "Unknown OriginIR bank"
      let a := bank.type.addressWidth
      unless arguments.length = a + bank.type.dataWidth do throw "Wrong OriginIR QRAM operand count"
      return .load name (← view registers (arguments.take a)) (← view registers (arguments.drop a))
    else
      let (name, wires) ← application line
      let some callee := modules.find? (fun m => m.name == name) | throw s!"Unsupported OriginIR operation: {name}"
      return .call name (← quantumArguments registers callee.registers wires)
        (banks.map Resource.name)

def statement (registers : List Register) (banks : List Resource) (modules : List Module)
    (line : String) : Except String Instruction := do
  match line.splitOn " controlled_by (" with
  | [body] => atomic registers banks modules body
  | [body, tail] =>
    let controls := splitArgs (← enclosed tail ")")
    unless !controls.isEmpty do throw "Empty OriginIR control set"
    return .control (← view registers controls) (2 ^ controls.length - 1)
      [← atomic registers banks modules body]
  | _ => throw "Malformed OriginIR controls"

def block (registers : List Register) (banks : List Resource) (modules : List Module)
    (lines : List String) : Except String (List Instruction) := do
  let stack ← lines.foldlM (init := ([[]] : List (List Instruction))) fun stack line =>
    match line, stack with
    | "DAGGER", _ => return [] :: stack
    | "ENDDAGGER", body :: parent :: rest => return (.adjoint body.reverse :: parent) :: rest
    | "ENDDAGGER", _ => throw "Unmatched OriginIR ENDDAGGER"
    | _, body :: rest => return ((← statement registers banks modules line) :: body) :: rest
    | _, [] => throw "Invalid OriginIR block frame"
  let [body] := stack | throw "Unclosed OriginIR DAGGER"
  return body.reverse

def parseModules (banks : List Resource) : Nat → List String → List Module →
    Except String (List Module × String)
  | 0, _, _ => .error "OriginIR module list exhausted"
  | _ + 1, [entry], modules => .ok (modules, entry)
  | fuel + 1, header :: tail, modules => do
    unless header.startsWith "DEF " do throw "Expected OriginIR DEF"
    let (name, formals) ← application (header.drop 4).toString
    let registers ← formals.mapM fun formal => do
      let (name, width) ← indexed formal
      unless 0 < width do throw "Zero-width OriginIR formal"
      return (⟨name, ⟨.bits, width⟩⟩ : Register)
    let lines := tail.takeWhile (· != "ENDDEF")
    let "ENDDEF" :: rest := tail.drop lines.length | throw "Missing OriginIR ENDDEF"
    let body ← block registers banks modules lines
    parseModules banks fuel rest (modules ++ [⟨name, registers, banks, some body, [], []⟩])
  | _ + 1, [], _ => .error "Missing OriginIR entry call"

/-- Decode the exported target. All physical wires, including workspace, are explicit.
The supported target instructions denote the matching gate, controlled gate, XOR read,
or adjoint on these wires. The decoder does not use the RIR source. -/
def parse (text : String) : Except String Program := do
  let lines := ((text.splitOn "\n").map trimmed).filter fun line => !line.isEmpty
  let declarations := lines.takeWhile fun line => line.startsWith "QRAMDECL "
  let banks ← declarations.mapM bankDecl
  let qubits :: "CREG 0" :: body := lines.drop declarations.length |
    throw "Expected OriginIR QINIT and CREG 0"
  unless qubits.startsWith "QINIT " do throw "Expected OriginIR QINIT"
  let width ← parseNat (qubits.drop 6).toString
  let (modules, entry) ← parseModules banks (body.length + 1) body []
  let registers : List Register := [⟨"q", ⟨.bits, width⟩⟩]
  let (_, actuals) ← application entry
  unless actuals == (List.range width).map (fun i => s!"q[{i}]") do
    throw "OriginIR entry does not use the canonical physical wire order"
  let code ← statement registers banks modules entry
  let .call _ _ _ := code | throw "Expected an OriginIR entry module call"
  return ⟨"originir_entry", modules ++ [⟨"originir_entry", registers, banks, some [code], [], []⟩]⟩

noncomputable def matrix (text : String) (memory : Snapshot) :
    Except String (Σ width : Nat, WireMatrix width) :=
  (parse text).bind fun program => program.matrix memory

def isClosedInstruction : ResolvedInstruction → Bool
  | .query .. => false
  | .controlled _ inner | .adjoint inner => isClosedInstruction inner
  | _ => true

structure FlatCertificate (source : Program) (text : String) where
  target : Program
  decoded : parse text = .ok target
  sourceTrace : ResolvedProgram
  targetTrace : ResolvedProgram
  sourceResolved : source.resolve = .ok sourceTrace
  targetResolved : target.resolve = .ok targetTrace
  closed : sourceTrace.instructions.all isClosedInstruction = true
  agreement : sourceTrace.normalize = targetTrace.normalize

def checkFlat (source : Program) (text : String) : Except String (FlatCertificate source text) := do
  match decoded : parse text with
  | .error reason => throw reason
  | .ok target =>
    let s ← lookupModule source source.entry
    let t ← lookupModule target target.entry
    unless s.resources == t.resources do throw "OriginIR export changes the bank interface"
    match sourceResolved : source.resolve, targetResolved : target.resolve with
    | .ok src, .ok dst =>
      if closed : src.instructions.all isClosedInstruction then
        if agreement : src.normalize = dst.normalize then
          return ⟨target, decoded, src, dst, sourceResolved, targetResolved, closed, agreement⟩
        else throw "OriginIR export changes the normalized instruction sequence"
      else throw "OriginIR translation validation requires closed RIR"
    | .error reason, _ | _, .error reason => throw reason

theorem FlatCertificate.sound {source : Program} {text : String}
    (cert : FlatCertificate source text) (memory : Snapshot) :
    matrix text memory = source.matrix memory := by
  have normalized (trace : ResolvedProgram) :
      (do let u ← trace.normalize.matrix memory
          pure (⟨trace.normalize.wireCount, u⟩ : Σ n, WireMatrix n)) =
      (do let u ← trace.matrix memory
          pure (⟨trace.wireCount, u⟩ : Σ n, WireMatrix n)) := by
    change (do let u ← trace.normalize.matrix memory
               pure (⟨trace.wireCount, u⟩ : Σ n, WireMatrix n)) = _
    rw [ResolvedProgram.normalize_matrix]
    rfl
  unfold matrix Program.matrix
  rw [cert.decoded]
  simp only [Except.bind, Bind.bind]
  rw [cert.targetResolved, cert.sourceResolved]
  change (do let u ← cert.targetTrace.matrix memory
             pure (⟨cert.targetTrace.wireCount, u⟩ : Σ n, WireMatrix n)) =
    (do let u ← cert.sourceTrace.matrix memory
        pure (⟨cert.sourceTrace.wireCount, u⟩ : Σ n, WireMatrix n))
  rw [← normalized cert.targetTrace, ← normalized cert.sourceTrace, cert.agreement]

/-- Zero-extend a public input in the canonical layout used by the exporter. -/
def publicFrame (sourceWidth targetWidth : Nat) (fits : sourceWidth ≤ targetWidth) :
    Reg sourceWidth ↪ Reg targetWidth where
  toFun x i := if h : i.val < sourceWidth then x ⟨i.val, h⟩ else false
  inj' := by
    intro x y same
    funext i
    have bit := congrFun same (Fin.castLE fits i)
    simpa [Fin.castLE] using bit

structure WorkspaceCertificate (source : Program) (text : String) (image : Json) where
  target : Program
  decoded : parse text = .ok target
  original : Verification.ReversibleFrame.Certificate source image 10
  exported : Verification.ReversibleFrame.Certificate target image 10
  sameSnapshot : original.snapshot = exported.snapshot
  fits : original.graph.entryWires ≤ exported.graph.entryWires
  agreement : ∀ input : Reg original.graph.entryWires,
    let place := publicFrame _ _ fits
    BasisWord.perm exported.gate.action (place input) =
      place (BasisWord.perm original.gate.action input)

def checkSameSnapshot {source target : Program} {image : Json}
    (original : Verification.ReversibleFrame.Certificate source image 10)
    (exported : Verification.ReversibleFrame.Certificate target image 10) :
    Except String (Subtype fun _ : Unit => original.snapshot = exported.snapshot) := do
  let src := original.graph
  let dst := exported.graph
  match srcFound : lookup (src.modules.map fun m => (m.name, m)) src.entry "scoped entry",
        dstFound : lookup (dst.modules.map fun m => (m.name, m)) dst.entry "scoped entry" with
  | .ok srcEntry, .ok dstEntry =>
    if same : srcEntry.banks = dstEntry.banks then
      have decoded := ScopedProgram.decodeSnapshot_congr_banks image srcFound dstFound same
      return ⟨(), Except.ok.inj (original.decoded.symm.trans (decoded.trans exported.decoded))⟩
    else throw "OriginIR export changes the resolved bank interface"
  | .error reason, _ | _, .error reason => throw reason

def checkWorkspace (source : Program) (text : String) (image : Json) :
    Except String (WorkspaceCertificate source text image) := do
  match decoded : parse text with
  | .error reason => throw reason
  | .ok target =>
    let s ← lookupModule source source.entry
    let t ← lookupModule target target.entry
    unless s.resources == t.resources do throw "OriginIR export changes the bank interface"
    let original ← Verification.ReversibleFrame.certify source image 10
    let exported ← Verification.ReversibleFrame.certify target image 10
    unless original.graph.entryWires ≤ 10 && exported.graph.entryWires ≤ 12 do
      throw "OriginIR workspace checking is limited to ten public and twelve physical wires"
    let snapshot ← checkSameSnapshot original exported
    if fits : original.graph.entryWires ≤ exported.graph.entryWires then
      if agreement : ∀ input : Reg original.graph.entryWires,
          let place := publicFrame _ _ fits
          BasisWord.perm exported.gate.action (place input) =
            place (BasisWord.perm original.gate.action input) then
        return ⟨target, decoded, original, exported, snapshot.property, fits, agreement⟩
      else throw "OriginIR changes the public action or leaves nonzero workspace"
    else throw "OriginIR has too few physical wires"

private theorem permutationFrame {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (original : S → S) (exported : T → T) (place : S ↪ T)
    (agree : ∀ input, exported (place input) = place (original input)) :
    permMatrix exported * basisFrame place = basisFrame place * permMatrix original := by
  ext row col
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [permMatrix, basisFrame, mul_ite, agree]

/-- The public-register interpretation of the physical target circuit. Its program
has every wire exposed, including the wires used as source workspace. -/
noncomputable def scopedMatrix (text : String) (memory : Snapshot) :
    Except String (Σ width : Nat, WireMatrix width) :=
  (parse text).bind fun program => program.scopedMatrix memory

theorem WorkspaceCertificate.sound {source : Program} {text : String} {image : Json}
    (cert : WorkspaceCertificate source text image) :
    source.scopedMatrix cert.original.snapshot =
      .ok ⟨cert.original.graph.entryWires, cert.original.gate.matrix⟩ ∧
    scopedMatrix text cert.original.snapshot =
      .ok ⟨cert.exported.graph.entryWires, cert.exported.gate.matrix⟩ ∧
    let frame := basisFrame (publicFrame _ _ cert.fits)
    cert.exported.gate.matrix * frame = frame * cert.original.gate.matrix := by
  refine ⟨cert.original.sound, ?_, permutationFrame _ _ _ cert.agreement⟩
  rw [scopedMatrix, cert.decoded, cert.sameSnapshot]
  exact cert.exported.sound

end OracqVerify.RIR.OriginIR
