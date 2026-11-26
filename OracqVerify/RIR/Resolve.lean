module

public import OracqVerify.RIR.Syntax

/-! Resolve named calls and views against the entry wire and QRAM interfaces. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

variable {α : Type}

/-- A call frame maps register names to low-to-high entry wires and resource names to entry handles. -/
structure Frame where
  registers : List (String × List Nat)
  resources : List (String × Resource)
  deriving Repr

/-- An ordered predicate on entry wires, with wire zero of the view the least significant bit. -/
structure Guard where
  wires : List Nat
  value : Nat
  deriving DecidableEq, Repr

inductive ResolvedInstruction where
  | unary (gate : UnaryGate) (wires : List Nat)
  | gphase (angle : Lean.JsonNumber)
  | xor (source target : List Nat)
  | addConst (wires : List Nat) (amount : Nat)
  | load (bank : Resource) (address data : List Nat)
  | query (slot : String) (arguments : List (List Nat)) (banks : List Resource)
  | controlled (guard : Guard) (instruction : ResolvedInstruction)
  | adjoint (instruction : ResolvedInstruction)
  deriving DecidableEq, Repr

structure ResolvedProgram where
  wireCount : Nat
  instructions : List ResolvedInstruction
  deriving DecidableEq, Repr

def lookup (entries : List (String × α)) (name : String) (kind : String) :
    Except String α :=
  match entries.lookup name with
  | some value => .ok value
  | none => .error s!"Unknown {kind} {name}"

/-- Read the bits of local spans through the caller's layout without reordering them. -/
def resolveRef (frame : Frame) (ref : Ref) : Except String (List Nat) := do
  let pieces ← ref.parts.mapM fun span => do
    let source ← lookup frame.registers span.register "register"
    unless span.start + span.width ≤ source.length do
      throw s!"Span outside register {span.register}"
    return (source.drop span.start).take span.width
  let wires := pieces.flatten
  unless wires.length = ref.type.width do throw "View width does not match its spans"
  unless wires.Nodup do throw "View contains duplicate wires"
  return wires

/-- Bind quantum and resource formals in signature order. Bank handles can be shared. -/
def resolveCall (caller : Frame) (callee : Module) (arguments : List Ref)
    (resources : List String) : Except String Frame := do
  unless arguments.length = callee.registers.length do throw "Wrong quantum call arity"
  unless resources.length = callee.resources.length do throw "Wrong resource call arity"
  let registers ← (callee.registers.zip arguments).mapM fun (formal, actual) => do
    unless formal.type = actual.type do throw s!"Register type mismatch at {formal.name}"
    return (formal.name, ← resolveRef caller actual)
  unless (registers.flatMap Prod.snd).Nodup do
    throw "Call arguments overlap"
  let banks ← (callee.resources.zip resources).mapM fun (formal, actual) => do
    let bank ← lookup caller.resources actual "QRAM parameter"
    unless formal.type = bank.type do throw s!"QRAM type mismatch at {formal.name}"
    return (formal.name, bank)
  return ⟨registers, banks⟩

def rootRegisters (registers : List Register) (offset : Nat) :
    List (String × List Nat) :=
  match registers with
  | [] => []
  | reg :: rest =>
    (reg.name, (List.range reg.type.width).map (offset + ·)) ::
      rootRegisters rest (offset + reg.type.width)

def lookupModule (program : Program) (name : String) : Except String Module :=
  match program.modules.find? (fun m => m.name == name) with
  | some target => .ok target
  | none => .error s!"Unknown module {name}"

def checkInterface (m : Module) : Except String Unit := do
  unless (((m.registers ++ m.locals).map Register.name) ++ m.resources.map Resource.name).Nodup do
    throw s!"Duplicate interface name in {m.name}"
  unless m.registers.any (fun reg => reg.type.width > 0) do
    throw s!"Empty quantum interface in {m.name}"
  for bank in m.resources do
    unless bank.type.addressWidth > 0 && bank.type.dataWidth > 0 do
      throw s!"Zero-width QRAM interface in {m.name}"
  if m.body.isNone then
    unless m.locals.isEmpty do throw s!"Open declaration has local workspace in {m.name}"
    match m.attributes.lookup "oracle_paradigm" with
    | some (.str _) => pure ()
    | _ => throw s!"Missing oracle paradigm for {m.name}"

structure ResolveContext where
  guards : List Guard := []
  inverse : Bool := false
  invokedAdjoint : Bool := false

def ResolveContext.emit (context : ResolveContext) (instruction : ResolvedInstruction) :
    ResolvedInstruction :=
  context.guards.foldr ResolvedInstruction.controlled
    (if context.inverse then .adjoint instruction else instruction)

def ResolveContext.checkProtected (context : ResolveContext) (wires : List Nat) :
    Except String Unit :=
  if ((context.guards.flatMap Guard.wires) ++ wires).Nodup then .ok ()
  else .error "Operation overlaps a protected control wire"

def checkCapability (callee : Module) (key : String) (needed : Bool) :
    Except String Unit :=
  if needed then
    match callee.attributes.lookup key with
    | none | some (.bool true) => .ok ()
    | _ => .error s!"Module {callee.name} lacks {key}"
  else .ok ()

def resolveInstruction (frame : Frame)
    (follow : String → List Ref → List String → ResolveContext →
      Except String (List ResolvedInstruction))
    (enterBlock : ResolveContext → List Instruction → Except String (List ResolvedInstruction))
    (context : ResolveContext) : Instruction → Except String (List ResolvedInstruction)
  | .unary gate target => do
    let wires ← resolveRef frame target
    context.checkProtected wires
    return [context.emit (.unary gate wires)]
  | .phase angle target => do
    let wires ← resolveRef frame target
    context.checkProtected wires
    let nodes := if context.inverse then wires.reverse else wires
    return nodes.map fun wire => context.emit (.controlled ⟨[wire], 1⟩ (.gphase angle))
  | .gphase angle => .ok [context.emit (.gphase angle)]
  | .xor src dst => do
    let source ← resolveRef frame src
    let target ← resolveRef frame dst
    unless source.length = target.length ∧ (source ++ target).Nodup do
      throw "XOR requires disjoint operands of equal width"
    context.checkProtected (source ++ target)
    return [context.emit (.xor source target)]
  | .swap first second => do
    let xs ← resolveRef frame first
    let ys ← resolveRef frame second
    unless xs.length = ys.length ∧ (xs ++ ys).Nodup do
      throw "Swap requires disjoint operands of equal width"
    context.checkProtected (xs ++ ys)
    return [.xor xs ys, .xor ys xs, .xor xs ys].map context.emit
  | .addConst target amount => do
    unless target.type.kind = .uint do throw "Constant addition requires an unsigned register view"
    let wires ← resolveRef frame target
    unless amount < 2 ^ wires.length do throw "Constant addition exceeds the register range"
    context.checkProtected wires
    return [context.emit (.addConst wires amount)]
  | .load resource address data => do
    let bank ← lookup frame.resources resource "QRAM parameter"
    let a ← resolveRef frame address
    let d ← resolveRef frame data
    unless a.length = bank.type.addressWidth ∧ d.length = bank.type.dataWidth do
      throw s!"QRAM operand width mismatch for {resource}"
    unless (a ++ d).Nodup do throw "QRAM address and data overlap"
    context.checkProtected d
    return [context.emit (.load bank a d)]
  | .call name arguments resources => follow name arguments resources context
  | .control register value inner => do
    let wires ← resolveRef frame register
    unless !wires.isEmpty && value < 2 ^ wires.length do
      throw "Control requires a nonempty view and an in-range value"
    context.checkProtected wires
    enterBlock { context with guards := context.guards ++ [⟨wires, value⟩] } inner
  | .adjoint inner => enterBlock { context with inverse := !context.inverse } inner
  | .repeat count inner => do
    let steps ← enterBlock context inner
    if steps.isEmpty then return []
    unless count * steps.length ≤ 100000 do
      throw "Repeat expands to more than 100000 resolved instructions"
    return (List.replicate count steps).flatten

def resolveBlock (frame : Frame)
    (follow : String → List Ref → List String → ResolveContext →
      Except String (List ResolvedInstruction)) :
    Nat → ResolveContext → List Instruction → Except String (List ResolvedInstruction)
  | 0, _, [] => .ok []
  | 0, _, _ => .error "RIR block nesting exceeds 127"
  | fuel + 1, context, body => do
    let nodes := if context.inverse then body.reverse else body
    let resolved ← nodes.mapM
      (resolveInstruction frame follow (resolveBlock frame follow fuel) context)
    return resolved.flatten

/-- Unfold the entry block once, without unfolding its recursive block callback. -/
theorem resolveBlock_root (frame : Frame)
    (follow : String → List Ref → List String → ResolveContext →
      Except String (List ResolvedInstruction))
    (context : ResolveContext) (body : List Instruction) :
    resolveBlock frame follow 128 context body = (do
      let nodes := if context.inverse then body.reverse else body
      let resolved ← nodes.mapM
        (resolveInstruction frame follow (resolveBlock frame follow 127) context)
      return resolved.flatten) := rfl

def resolveModule (program : Program) : Nat → Module → Frame → ResolveContext →
    Except String (List ResolvedInstruction)
  | 0, _, _, _ => .error "Cyclic module call"
  | fuel + 1, m, frame, context => do
    unless m.locals.isEmpty do throw "Module-local workspace requires scoped resolution"
    let some body := m.body |
      return [context.emit (.query m.name (frame.registers.map Prod.snd)
        (frame.resources.map Prod.snd))]
    let follow name arguments resources callContext := do
        let callee ← lookupModule program name
        let child ← resolveCall frame callee arguments resources
        callContext.checkProtected (child.registers.flatMap Prod.snd)
        checkCapability callee "supports_controlled" (!callContext.guards.isEmpty)
        let needsAdjoint := callContext.inverse || callContext.invokedAdjoint
        checkCapability callee "supports_adjoint" needsAdjoint
        resolveModule program fuel callee child { callContext with invokedAdjoint := needsAdjoint }
    resolveBlock frame follow 128 context body

/-- Resolve the entry's reachable body. Preserve open calls as explicit query instructions. -/
def Program.resolve (program : Program) : Except String ResolvedProgram := do
  unless (program.modules.map Module.name).Nodup do throw "Duplicate module"
  program.modules.forM checkInterface
  let entry ← lookupModule program program.entry
  let frame := ⟨rootRegisters entry.registers 0,
    entry.resources.map (fun bank => (bank.name, bank))⟩
  let instructions ← resolveModule program program.modules.length entry frame {}
  let wireCount := entry.registers.foldl (fun count reg => count + reg.type.width) 0
  return ⟨wireCount, instructions⟩

end OracqVerify.RIR
