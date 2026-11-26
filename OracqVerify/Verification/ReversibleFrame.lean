module

public import OracqVerify.RIR.ReversibleProgram
public import OracqVerify.RIR.ScopedSourceLink
public import OracqVerify.RIR.SnapshotImage

/-! Successful frame checking denotes a clean, reversible scoped matrix. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.ReversibleFrame

open Lean RIR

def decodeHints (json : Json) : Except String ReversibleHints := do
  let entries ← json.getObj?
  let decoded ← entries.toList.mapM fun (name, value) => do
    let hint : BasisHints ← fromJson? value
    return (name, hint)
  return fun name => (decoded.lookup name).getD {}

structure Certificate (source : Program) (image : Json) (limit : Nat)
    (hints : ReversibleHints := fun _ => {}) where
  graph : ScopedProgram
  resolved : source.resolveScoped = .ok graph
  snapshot : Snapshot
  decoded : graph.decodeSnapshot image = .ok snapshot
  gate : ReversibleGate graph.entryWires
  compiled : graph.compileReversibleGate snapshot (some limit) hints = .ok gate

def certify (source : Program) (image : Json) (limit : Nat)
    (hints : ReversibleHints := fun _ => {}) :
    Except String (Certificate source image limit hints) := do
  match resolved : source.resolveScoped with
  | .error reason => throw reason
  | .ok graph =>
    match decoded : graph.decodeSnapshot image with
    | .error reason => throw reason
    | .ok snapshot =>
      match compiled : graph.compileReversibleGate snapshot (some limit) hints with
      | .error reason => throw reason
      | .ok gate => return ⟨graph, resolved, snapshot, decoded, gate, compiled⟩

theorem Certificate.sound {source : Program} {image : Json} {limit : Nat} {hints : ReversibleHints}
    (cert : Certificate source image limit hints) :
    source.scopedMatrix cert.snapshot = .ok ⟨cert.graph.entryWires, cert.gate.matrix⟩ :=
  Program.scopedMatrix_of_resolved cert.resolved
    (cert.graph.compileReversibleGate_sound cert.snapshot cert.gate cert.compiled)

end OracqVerify.Verification.ReversibleFrame
