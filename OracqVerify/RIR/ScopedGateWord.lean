module

public import OracqVerify.RIR.ScopedRoot
public import OracqVerify.RIR.ReversibleProgram

/-! Connect certified flat gate words to a scoped definition or an identity alias. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

def gateModule (name : String) (wires : Nat) (steps : List ResolvedInstruction) : ScopedModule :=
  ⟨name, wires, 0, [], some steps, 0, true, true⟩

def directGateGraph (name : String) (wires : Nat) (steps : List ResolvedInstruction) : ScopedProgram :=
  ⟨name, [gateModule name wires steps], wires, 0⟩

def forwardedGateGraph (name inner : String) (wires : Nat)
    (arguments : List (List Nat)) (steps : List ResolvedInstruction) : ScopedProgram :=
  ⟨name, [gateModule inner wires steps,
    gateModule name wires [.query inner arguments []]], wires, 0⟩

theorem Program.resolved_of_flat_matrix {source : Program} {wires : Nat} {steps : List ResolvedInstruction}
    {memory : Snapshot} {u : WireMatrix wires}
    (resolved : source.resolve = .ok ⟨wires, steps⟩)
    (evaluated : source.matrix memory = .ok ⟨wires, u⟩) :
    (ResolvedProgram.mk wires steps).matrix memory = .ok u := by
  cases computed : (ResolvedProgram.mk wires steps).matrix memory <;>
    simp_all [Program.matrix, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem directGateGraph_matrix (name : String) (wires : Nat) (steps : List ResolvedInstruction)
    (memory : Snapshot) (valid : steps.all (ResolvedInstruction.isUnitaryGate wires) = true)
    {u : WireMatrix wires} (evaluated : (ResolvedProgram.mk wires steps).matrix memory = .ok u) :
    (directGateGraph name wires steps).matrixWith memory = .ok u := by
  let graph := directGateGraph name wires steps
  let root : ScopedRoot graph wires [] :=
    ⟨[], gateModule name wires steps, rfl, rfl, rfl, rfl, rfl,
      by simp [graph, directGateGraph, gateModule, lookup]⟩
  exact root.matrix_of_node memory
    (ScopedModule.interpret_gateWord name wires [] steps 0 true true memory [] valid evaluated)

theorem forwardedGateGraph_matrix (name inner : String) (wires : Nat)
    (arguments : List (List Nat)) (steps : List ResolvedInstruction)
    (ordered : arguments.flatten = List.range wires)
    (memory : Snapshot) (valid : steps.all (ResolvedInstruction.isUnitaryGate wires) = true)
    {u : WireMatrix wires}
    (evaluated : (ResolvedProgram.mk wires steps).matrix emptySnapshot = .ok u)
    (names : name ≠ inner) :
    (forwardedGateGraph name inner wires arguments steps).matrixWith memory = .ok u := by
  let child := gateModule inner wires steps
  let wrapper := gateModule name wires [.query inner arguments []]
  let graph := forwardedGateGraph name inner wires arguments steps
  have different : (name == inner) = false := Bool.eq_false_iff.mpr fun eq => names (eq_of_beq eq)
  let root : ScopedRoot graph wires [] :=
    ⟨[child], wrapper, rfl, rfl, rfl, rfl, rfl,
      by simp [graph, forwardedGateGraph, wrapper, gateModule, lookup, List.lookup, different]⟩
  have childComputed : child.interpret [] emptySnapshot = .ok u :=
    ScopedModule.interpret_gateWord inner wires [] steps 0 true true emptySnapshot [] valid evaluated
  have selected :
      lookup root.known inner "scoped callee" = .ok ⟨wires, [], child.interpret []⟩ :=
    lookup_scoped_definition [] [] child (by simp) "scoped callee"
  have layout : View.ofWires wires wires arguments.flatten = .ok (Function.Embedding.refl (Fin wires)) :=
    ordered ▸ View.ofWires_range wires
  have forwarded : memory.forward [] [] = .ok emptySnapshot := rfl
  have call : root.known.atCall wires memory ⟨inner, arguments, []⟩ = .ok u := by
    change (do
      let definition ← lookup root.known inner "scoped callee"
      let view ← View.ofWires wires definition.publicWires arguments.flatten
      let snap ← memory.forward definition.banks []
      let body ← definition.apply snap
      return view.placeMatrix body) = _
    rw [selected]
    simp only [Bind.bind, Except.bind, layout, forwarded, childComputed, Pure.pure, Except.pure,
      View.placeMatrix_refl]
  have body : wrapper.bodyMatrix memory (root.known.atCall wires memory) = .ok u := by
    change ((([.query inner arguments []] : List ResolvedInstruction).mapM
      (ResolvedInstruction.matrixWith wires memory (root.known.atCall wires memory))).map wordMatrix) =
      .ok u
    simp [ResolvedInstruction.matrixWith, call, List.mapM_cons, Bind.bind, Except.bind,
      Pure.pure, Except.pure, Except.map, wordMatrix]
  have interpreted := ScopedModule.interpret_zero_locals name wires []
    (some [.query inner arguments []]) 0 true true memory root.known
    (ScopedModule.interpret_unitary childComputed) body
  exact root.matrix_of_node memory interpreted

end OracqVerify.RIR
