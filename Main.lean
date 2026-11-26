module

public import OracqVerify.Generators.Registry
public import OracqVerify.RIR.ScopedSourceLink
public import OracqVerify.RIR.ScopedSubgraph
public import OracqVerify.Verification.ReversibleFrame
public import OracqVerify.RIR.SourceLink
import OracqVerify.RIR.SourceSemantics
import OracqVerify.RIR.OriginIR
import OracqVerify.Verification.Grover
import OracqVerify.Verification.WideGroverBinding
import OracqVerify.Verification.ApproximatePhase
import OracqVerify.Verification.SparseBlockReplacement
import OracqVerify.Verification.LCHSLink
import OracqVerify.Verification.WideLCHS
import OracqVerify.Verification.AmplificationReplacement

set_option warningAsError true

public section

open Lean OracqVerify.Generators OracqVerify.RIR

private def usage : String :=
  "Usage:\n" ++
  "  oracq-verify list\n" ++
  "  oracq-verify generate <theorem> <arguments>\n" ++
  "  oracq-verify resolve <file>\n" ++
  "  oracq-verify check-source <program-file>\n" ++
  "  oracq-verify check-originir <program-file> <originir-file> [<snapshot-file>]\n" ++
  "  oracq-verify check-grover <gate|qram> <open-file> <bound-file> <snapshot-file> [<iterations>]\n" ++
  "  oracq-verify check-grover-wide <gate|qram> <width> <iterations> <open-file> <bound-file> <snapshot-file>\n" ++
  "  oracq-verify check-approx-phase <open-file> <bound-file> <reference-angle> <rounds> <error-limit>\n" ++
  "  oracq-verify check-replacement sparse <gate|qram> <open-file> <bound-file> <snapshot-file>\n" ++
  "  oracq-verify check-replacement lchs <baseline-file> <candidate-file>\n" ++
  "  oracq-verify check-lchs-components <program-file>\n" ++
  "  oracq-verify check-lchs-link <open-file> <bound-file> [<bound-file> ...]\n" ++
  "  oracq-verify check-lchs-wide <data-width> <open-file> <bound-file> [<bound-file> ...]\n" ++
  "  oracq-verify check-replacement amplification <open-file> <bound-file> <input-file>\n" ++
  "  oracq-verify check-link <open-file> <bound-file> [<capture-plan-file>]\n" ++
  "  oracq-verify check-scoped-link <open-file> <bound-file> [<scoped-capture-plan-file>]\n" ++
  "  oracq-verify check-reversible-frame <program-file> <image-file> <max-enumerated-wires>\n" ++
  "  oracq-verify verify <theorem> <open-file> <arguments>\n" ++
  "  oracq-verify verify-bound <theorem> <open-file> <bound-file> <parameter> [<memory-file>]"

private def encodeResolved : ResolvedInstruction → Json
  | .unary gate wires =>
    let fields := [("op", toJson (gateName gate)), ("wires", toJson wires)]
    match gateAngle gate with
    | .null => Json.mkObj fields
    | angle => Json.mkObj (("angle", angle) :: fields)
  | .gphase angle => Json.mkObj [("op", toJson "gphase"), ("angle", .num angle)]
  | .xor source target =>
    Json.mkObj [("op", toJson "xor"), ("source", toJson source), ("target", toJson target)]
  | .addConst wires amount =>
    Json.mkObj [("op", toJson "add_const"), ("wires", toJson wires), ("amount", toJson amount)]
  | .load bank address data => Json.mkObj [("op", toJson "load"), ("bank", toJson bank.name),
      ("address", toJson address), ("data", toJson data)]
  | .query slot arguments banks => Json.mkObj [("op", toJson "query"), ("slot", toJson slot),
      ("arguments", toJson arguments), ("banks", toJson (banks.map Resource.name))]
  | .controlled guard instruction => Json.mkObj [("op", toJson "control"),
      ("wires", toJson guard.wires), ("value", toJson guard.value),
      ("instruction", encodeResolved instruction)]
  | .adjoint instruction =>
    Json.mkObj [("op", toJson "adjoint"), ("instruction", encodeResolved instruction)]

private def encodeScopedModule (m : ScopedModule) : Json :=
  let banks := m.banks.map fun bank => Json.mkObj [("name", toJson bank.name),
    ("address_width", toJson bank.type.addressWidth), ("data_width", toJson bank.type.dataWidth)]
  Json.mkObj [("name", toJson m.name), ("public_wires", toJson m.publicWires),
    ("local_wires", toJson m.localWires), ("peak_local_wires", toJson m.peakLocals),
    ("banks", toJson banks), ("supports_controlled", toJson m.supportsControlled),
    ("supports_adjoint", toJson m.supportsAdjoint),
    ("instructions", toJson (m.body.map (List.map encodeResolved)))]

private def resolveJson (text : String) : Except String Json := do
  let program ← Program.fromJson (← Json.parse text)
  if program.modules.any (fun m => !m.locals.isEmpty) then
    let resolved ← program.resolveScoped
    return Json.mkObj [("mode", toJson "scoped"), ("entry", toJson resolved.entry),
      ("wire_count", toJson resolved.entryWires), ("peak_local_wires", toJson resolved.peakLocals),
      ("modules", toJson (resolved.modules.map encodeScopedModule))]
  let resolved ← program.resolve
  return Json.mkObj [("wire_count", toJson resolved.wireCount),
    ("instructions", .arr (resolved.instructions.toArray.map encodeResolved))]

private def report (result : Except String Json) : IO UInt32 := do
  match result with
  | .ok output =>
    IO.println output.compress
    return 0
  | .error reason =>
    IO.eprintln reason
    return 1

private def parseProgram (contents : String) : Except String Program := do
  Program.fromJson (← Json.parse contents)

private def widthPredecessor (value : String) : Except String Nat := do
  match value.toNat? with
  | some (n+1) => pure n
  | _ => throw "Expected a positive width"

private def verifyApproxPhase (sourcePath boundPath angleText count limitText : String) : IO UInt32 := do
  try
    let source ← IO.FS.readFile sourcePath
    let bound ← IO.FS.readFile boundPath
    report (do
      let .num reference ← Json.parse angleText | throw "Expected a decimal reference angle"
      let .num limit ← Json.parse limitText | throw "Expected a decimal error limit"
      let some rounds := count.toNat? | throw "Expected a positive round count"
      unless 0 < rounds do throw "Expected a positive round count"
      let certificate ← OracqVerify.Verification.ApproximatePhase.certify
        (← parseProgram source) (← parseProgram bound) reference rounds
      let slotError := OracqVerify.Verification.ApproximatePhase.error reference certificate.angle
      let total := OracqVerify.Verification.ApproximatePhase.totalError reference certificate.angle rounds
      unless total ≤ rationalAngle limit do
        throw s!"Linked phase error {total} exceeds the requested limit"
      return Json.mkObj [("verified", toJson true), ("mode", toJson "approx-phase"),
        ("rounds", toJson rounds), ("slot_calls", toJson (2*rounds)),
        ("slot_error", toJson (toString slotError)), ("operator_error", toJson (toString total))])
  catch error => report (.error (toString error))

private def verifyWideGrover (variant width count openPath boundPath snapshotPath : String) : IO UInt32 := do
  try
    let source := parseProgram (← IO.FS.readFile openPath)
    let bound := parseProgram (← IO.FS.readFile boundPath)
    let image := Json.parse (← IO.FS.readFile snapshotPath)
    report (do
      let w ← widthPredecessor width
      let some iterations := count.toNat? | throw "Expected a positive iteration count"
      let impl : OracqVerify.Verification.WideGrover.Implementation ←
        match variant with
        | "gate" => pure .gate
        | "qram" => pure .qram
        | _ => throw "Expected gate or qram"
      let cert ← OracqVerify.Verification.WideGrover.certify (← source) (← bound) (← image) w iterations impl
      return Json.mkObj [("verified", toJson true), ("mode", toJson "grover-wide"),
        ("implementation", toJson variant), ("address_wires", toJson cert.link.closed.entryWires),
        ("peak_private_wires", toJson cert.link.closed.peakLocals), ("marked_address", toJson (2^w : Nat)),
        ("iterations", toJson iterations), ("qram_reads", toJson (if impl.isQram then 2*iterations else 0)),
        ("success_probability", toJson s!"sin^2((2*{iterations}+1)*arcsin(1/sqrt(2^{w+1})))")])
  catch error => report (.error (toString error))

private def verifyWideLCHS (width sourcePath : String) (paths : List String) : IO UInt32 := do
  try
    let source := parseProgram (← IO.FS.readFile sourcePath)
    let candidates ← paths.mapM fun path => do
      pure (parseProgram (← IO.FS.readFile path))
    report (do
      let d ← widthPredecessor width
      let caller ← OracqVerify.Verification.WideLCHS.certifyCaller (← source)
      let candidates ← candidates.mapM fun candidate => do
        let cert ← OracqVerify.Verification.WideLCHS.certify caller (← candidate) d
        return Json.mkObj [("wires", toJson cert.trace.wireCount),
          ("resolved_instructions", toJson cert.trace.instructions.length),
          ("quadrature_error", toJson "1/50")]
      return Json.mkObj [("verified", toJson true), ("mode", toJson "lchs-wide"),
        ("data_wires", toJson (d+1)), ("selector_certificates", toJson 1),
        ("shared_slots", toJson caller.core.slots.toList), ("bindings", toJson candidates)])
  catch error => report (.error (toString error))

private def decodeCapturePlan (json : Json) : Except String CapturePlan := do
  let entries ← json.getObj?
  entries.toList.mapM fun (slot, value) => do
    let actuals ← value.getArr?
    let layout ← actuals.toList.mapM fun item =>
      match item with
      | .num _ => BankActual.original <$> item.getNat?
      | _ => do
        let name ← item.getObjValAs? String "name"
        let address ← item.getObjValAs? Nat "address_width"
        let data ← item.getObjValAs? Nat "data_width"
        return BankActual.captured ⟨name, ⟨address, data⟩⟩
    return (slot, layout)

private def decodeScopedCapturePlan (json : Json) : Except String ScopedCapturePlan := do
  let entries ← json.getObj?
  entries.toList.mapM fun (caller, plans) => return (caller, ← decodeCapturePlan plans)

private def checkLinkFiles (openPath boundPath : String) (planPath : Option String) : IO UInt32 := do
  try
    let source := parseProgram (← IO.FS.readFile openPath)
    let bound := parseProgram (← IO.FS.readFile boundPath)
    let plan ← match planPath with
      | some path => pure ((Json.parse (← IO.FS.readFile path)) >>= decodeCapturePlan)
      | none => pure (.ok [])
    report (do
      let link ← verifySourceLink (← source) (← bound) (← plan)
      let implementations := link.placed.map fun (site, word) => Json.mkObj [
        ("call", encodeResolved (.query site.name site.arguments site.banks)),
        ("implementation", toJson (word.map encodeResolved))]
      return Json.mkObj [("mode", toJson "structural-link"),
        ("wire_count", toJson link.boundary.wireCount),
        ("closed_instructions", toJson link.closed.instructions.length),
        ("implementations", toJson implementations)])
  catch error =>
    report (.error (toString error))

private def checkScopedLinkFiles (openPath boundPath : String) (planPath : Option String) :
    IO UInt32 := do
  try
    let source := parseProgram (← IO.FS.readFile openPath)
    let bound := parseProgram (← IO.FS.readFile boundPath)
    let plan ← match planPath with
      | some path => pure ((Json.parse (← IO.FS.readFile path)) >>= decodeScopedCapturePlan)
      | none => pure (.ok [])
    report (do
      let link ← verifyScopedSourceLink (← source) (← bound) (← plan)
      return Json.mkObj [("mode", toJson "structural-scoped-link"),
        ("wire_count", toJson link.exposed.entryWires),
        ("slots", toJson (scopedSlots link.caller)),
        ("caller", toJson (link.exposed.modules.map encodeScopedModule)),
        ("bound", toJson (link.closed.modules.map encodeScopedModule))])
  catch error =>
    report (.error (toString error))

private def verifyBoundFiles (theoremName openPath boundPath parameter : String)
    (memoryPath : Option String) : IO UInt32 := do
  try
    let openText ← IO.FS.readFile openPath
    let boundText ← IO.FS.readFile boundPath
    let memoryText ← match memoryPath with
      | some path => IO.FS.readFile path
      | none => pure "{}"
    report (do
      let original ← parseProgram openText
      let bound ← parseProgram boundText
      let memory ← Json.parse memoryText
      verifyBound theoremName [parameter] original bound memory)
  catch error =>
    report (.error (toString error))

private def verifyGroverFiles (variant openPath boundPath memoryPath : String)
    (iterations : Nat) : IO UInt32 := do
  try
    let source := parseProgram (← IO.FS.readFile openPath)
    let bound := parseProgram (← IO.FS.readFile boundPath)
    let image := Json.parse (← IO.FS.readFile memoryPath)
    report (do
      let implementation : OracqVerify.Verification.Grover.Implementation ←
        match variant with
        | "gate" => .ok .gate
        | "qram" => .ok .qram
        | _ => .error "Expected the Grover implementation to be gate or qram"
      let _ ← OracqVerify.Verification.Grover.certifyAt (← source) (← bound) (← image) implementation 3 iterations
      return Json.mkObj [("mode", toJson "grover"), ("implementation", toJson variant),
        ("marked_address", toJson (3 : Nat)), ("iterations", toJson iterations),
        ("success_probability", toJson (if iterations == 1 then "1" else s!"sin^2((2*{iterations}+1)*pi/6)")),
        ("qram_reads", toJson (if implementation.isQram then 2 * iterations else 0))])
  catch error =>
    report (.error (toString error))

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for entry in registry do
      IO.println s!"{entry.theoremName} {entry.usage}"
    return 0
  | "generate" :: theoremName :: parameters =>
    report ((generate theoremName parameters).map Program.toJson)
  | ["resolve", path] =>
    try
      report (resolveJson (← IO.FS.readFile path))
    catch error =>
      report (.error (toString error))
  | ["check-source", path] =>
    try
      let source := parseProgram (← IO.FS.readFile path)
      report (do
        let cert ← SourceSemantics.certify (← source)
        return Json.mkObj [("verified", toJson true), ("mode", toJson "source"),
          ("modules", toJson cert.resolved.modules.length), ("wires", toJson cert.resolved.entryWires)])
    catch error =>
      report (.error (toString error))
  | ["check-originir", path, targetPath] =>
    try
      let source := parseProgram (← IO.FS.readFile path)
      let contents ← IO.FS.readFile targetPath
      report (do
        let cert ← OriginIR.checkFlat (← source) contents
        return Json.mkObj [("verified", toJson true), ("mode", toJson "originir"),
          ("wires", toJson cert.targetTrace.wireCount)])
    catch error =>
      report (.error (toString error))
  | ["check-originir", path, targetPath, imagePath] =>
    try
      let source := parseProgram (← IO.FS.readFile path)
      let contents ← IO.FS.readFile targetPath
      let image := Json.parse (← IO.FS.readFile imagePath)
      report (do
        let cert ← OriginIR.checkWorkspace (← source) contents (← image)
        return Json.mkObj [("verified", toJson true), ("mode", toJson "originir-workspace"),
          ("public_wires", toJson cert.original.graph.entryWires),
          ("physical_wires", toJson cert.exported.graph.entryWires)])
    catch error =>
      report (.error (toString error))
  | ["check-grover", variant, openPath, boundPath, memoryPath] =>
    verifyGroverFiles variant openPath boundPath memoryPath 1
  | ["check-grover", variant, openPath, boundPath, memoryPath, count] =>
    match count.toNat? with
    | some iterations =>
      if 0 < iterations then verifyGroverFiles variant openPath boundPath memoryPath iterations
      else report (.error "Grover requires a positive iteration count")
    | none => report (.error "Grover requires a positive iteration count")
  | ["check-grover-wide", variant, width, count, openPath, boundPath, snapshotPath] =>
    verifyWideGrover variant width count openPath boundPath snapshotPath
  | ["check-approx-phase", sourcePath, boundPath, angle, rounds, limit] =>
    verifyApproxPhase sourcePath boundPath angle rounds limit
  | ["check-replacement", "sparse", variant, openPath, boundPath, imagePath] =>
    try
      let caller := parseProgram (← IO.FS.readFile openPath)
      let bound := parseProgram (← IO.FS.readFile boundPath)
      let image := Json.parse (← IO.FS.readFile imagePath)
      report (do
        unless variant == "gate" || variant == "qram" do throw "Expected the sparse variant gate or qram"
        let _ ← OracqVerify.Verification.SparseBlock.checkReplacement
          (← caller) (← bound) (← image) (variant == "qram")
        return Json.mkObj [("mode", toJson "sparse-block"), ("implementation", toJson variant),
          ("operator_error", toJson "0"), ("target_wires", toJson (2 : Nat)), ("signal_wires", toJson (1 : Nat))])
    catch error =>
      report (.error (toString error))
  | ["check-replacement", "lchs", baselinePath, candidatePath] =>
    try
      let baseline := parseProgram (← IO.FS.readFile baselinePath)
      let candidate := parseProgram (← IO.FS.readFile candidatePath)
      report (do
        let cert ← OracqVerify.Verification.LCHS.checkReplacement (← baseline) (← candidate)
        return Json.mkObj [("mode", toJson "lchs"), ("operator_error", toJson "47/100"),
          ("backend_discrepancy", toJson "1/1000"),
          ("baseline_wires", toJson cert.first.evidence.trace.wireCount),
          ("candidate_wires", toJson cert.second.evidence.trace.wireCount)])
    catch error =>
      report (.error (toString error))
  | ["check-lchs-components", path] =>
    try
      let source := parseProgram (← IO.FS.readFile path)
      report (do
        let cert ← OracqVerify.Verification.LCHS.certifyComponents (← source)
        return Json.mkObj [("verified", toJson true), ("mode", toJson "lchs-components"),
          ("nodes", toJson (4 : Nat)), ("branch_error", toJson "3/200"),
          ("assembly_error", toJson "1/10000000000"), ("quadrature_error", toJson "1/50"),
          ("wires", toJson cert.output.evidence.trace.wireCount)])
    catch error =>
      report (.error (toString error))
  | "check-lchs-wide" :: width :: openPath :: first :: rest =>
    verifyWideLCHS width openPath (first :: rest)
  | "check-lchs-link" :: openPath :: first :: rest =>
    try
      let source := parseProgram (← IO.FS.readFile openPath)
      let candidates ← (first :: rest).mapM fun path => do
        return parseProgram (← IO.FS.readFile path)
      report (do
        let caller ← OracqVerify.Verification.LCHS.certifyOpenAssembly (← source)
        let results ← candidates.mapM fun candidate => do
          let bound ← candidate
          let cert ← OracqVerify.Verification.LCHS.certifyLinkedAssembly caller bound
          return Json.mkObj [("wires", toJson cert.output.trace.wireCount),
            ("quadrature_error", toJson "1/50"), ("assembly_error", toJson "1/10000000000")]
        return Json.mkObj [("verified", toJson true), ("mode", toJson "lchs-link"),
          ("shared_slots", toJson caller.slots.toList), ("selector_certificates", toJson (1 : Nat)),
          ("bindings", toJson results)])
    catch error =>
      report (.error (toString error))
  | ["check-replacement", "amplification", openPath, boundPath, inputPath] =>
    try
      let caller := parseProgram (← IO.FS.readFile openPath)
      let bound := parseProgram (← IO.FS.readFile boundPath)
      let input := parseProgram (← IO.FS.readFile inputPath)
      report (do
        let _ ← OracqVerify.Verification.Amplification.checkReplacement (← caller) (← bound) (← input)
        return Json.mkObj [("mode", toJson "amplification"), ("initial_upper", toJson "31/100"),
          ("success_lower", toJson "97/100")])
    catch error =>
      report (.error (toString error))
  | ["check-link", openPath, boundPath] =>
    checkLinkFiles openPath boundPath none
  | ["check-link", openPath, boundPath, planPath] =>
    checkLinkFiles openPath boundPath (some planPath)
  | ["check-scoped-link", openPath, boundPath] =>
    checkScopedLinkFiles openPath boundPath none
  | ["check-scoped-link", openPath, boundPath, planPath] =>
    checkScopedLinkFiles openPath boundPath (some planPath)
  | ["check-reversible-frame", program, image, maxWires] =>
    try
      let source ← IO.FS.readFile program
      let contents ← IO.FS.readFile image
      report (do
        let some limit := maxWires.toNat? | throw "Invalid enumeration limit"
        let cert ← OracqVerify.Verification.ReversibleFrame.certify (← parseProgram source)
          (← Json.parse contents) limit
        return Json.mkObj [("mode", toJson "reversible-frame"),
          ("definitions", toJson cert.graph.modules.length),
          ("public_wires", toJson cert.graph.entryWires), ("peak_local_wires", toJson cert.graph.peakLocals),
          ("max_enumerated_wires", toJson limit)])
    catch error =>
      report (.error (toString error))
  | "verify" :: theoremName :: path :: parameters =>
    try
      report ((parseProgram (← IO.FS.readFile path)).bind (verify theoremName parameters))
    catch error =>
      report (.error (toString error))
  | ["verify-bound", theoremName, openPath, boundPath, parameter] =>
    verifyBoundFiles theoremName openPath boundPath parameter none
  | ["verify-bound", theoremName, openPath, boundPath, parameter, memory] =>
    verifyBoundFiles theoremName openPath boundPath parameter (some memory)
  | _ =>
    IO.eprintln usage
    return 1
