module

public import OracqVerify.RIR.Resolve

/-! Resolve scoped source into one relative frame per reachable module. -/

set_option warningAsError true

public section

namespace OracqVerify.RIR

/-- A module's public wires are followed by its private workspace. Calls in the
body carry actuals in this relative frame. An absent body is still an open slot. -/
structure ScopedModule where
  name : String
  publicWires : Nat
  localWires : Nat
  banks : List Resource
  body : Option (List ResolvedInstruction)
  peakLocals : Nat
  supportsControlled : Bool
  supportsAdjoint : Bool
  deriving DecidableEq, Repr

/-- A call graph with sibling reuse of stack workspace. -/
structure ScopedProgram where
  entry : String
  modules : List ScopedModule
  entryWires : Nat
  peakLocals : Nat
  deriving DecidableEq, Repr

private def registerWidth (registers : List Register) : Nat :=
  registers.foldl (fun count register => count + register.type.width) 0

private def supported (m : Module) (capability : String) : Bool :=
  (checkCapability m capability true).isOk

private def resolveDefinition (program : Program) (m : Module) :
    Except String (Option (List ResolvedInstruction)) := do
  let some body := m.body | return none
  let frame : Frame :=
    ⟨rootRegisters (m.registers ++ m.locals) 0, m.resources.map (fun bank => (bank.name, bank))⟩
  let follow name arguments resources context := do
    let callee ← lookupModule program name
    let child ← resolveCall frame callee arguments resources
    context.checkProtected (child.registers.flatMap Prod.snd)
    return [context.emit (.query name (child.registers.map Prod.snd) (child.resources.map Prod.snd))]
  return some (← resolveBlock frame follow 128 {} body)

private structure Dependency where
  name : String
  controlled : Bool := false
  adjointed : Bool := false

private def dependency : ResolvedInstruction → Option Dependency
  | .query name .. => some ⟨name, false, false⟩
  | .controlled _ step => (dependency step).map fun call => { call with controlled := true }
  | .adjoint step => (dependency step).map fun call => { call with adjointed := true }
  | _ => none

private abbrev ScopeCache := List (String × ScopedModule)

private def visitScope (program : Program) :
    Nat → String → ScopeCache → Except String (ScopedModule × ScopeCache)
  | 0, _, _ => .error "Cyclic module call"
  | fuel + 1, name, cache => do
    if let some resolved := cache.lookup name then return (resolved, cache)
    let m ← lookupModule program name
    let body ← resolveDefinition program m
    let mut checked := cache
    let mut descendants := 0
    let mut controlled := supported m "supports_controlled"
    let mut adjointed := supported m "supports_adjoint"
    for call in (body.getD []).filterMap dependency do
      let (child, updated) ← visitScope program fuel call.name checked
      unless !call.controlled || child.supportsControlled do
        throw s!"Subtree of {call.name} lacks supports_controlled"
      unless !call.adjointed || child.supportsAdjoint do
        throw s!"Subtree of {call.name} lacks supports_adjoint"
      checked := updated
      descendants := max descendants child.peakLocals
      controlled := controlled && child.supportsControlled
      adjointed := adjointed && child.supportsAdjoint
    let localWidth := registerWidth m.locals
    let resolved : ScopedModule :=
      ⟨name, registerWidth m.registers, localWidth, m.resources, body,
        localWidth + descendants, controlled, adjointed⟩
    return (resolved, (name, resolved) :: checked)

/-- Resolve reachable definitions without multiplying workspace or duplicating
module bodies by invocation count. The peak adds the current local width to
the largest reachable child peak. -/
def Program.resolveScoped (program : Program) : Except String ScopedProgram := do
  unless (program.modules.map Module.name).Nodup do throw "Duplicate module"
  program.modules.forM checkInterface
  let (root, cache) ← visitScope program program.modules.length program.entry []
  return ⟨program.entry, cache.reverse.map Prod.snd, root.publicWires, root.peakLocals⟩

end OracqVerify.RIR
