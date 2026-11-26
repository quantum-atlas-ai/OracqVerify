module

public import OracqVerify.RIR.ScopedSubgraph
public import OracqVerify.RIR.ScopedSourceLink

/-! Checked postorder roots for public execution and placement. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

/-- The last resolved definition supplies the entry and its lexical environment. -/
structure ScopedRoot (graph : ScopedProgram) (wires : Nat) (banks : List Resource) where
  previous : List ScopedModule
  node : ScopedModule
  order : graph.modules = previous ++ [node]
  name : node.name = graph.entry
  width : node.publicWires = wires
  entryWidth : graph.entryWires = wires
  resources : node.banks = banks
  decodedNode : lookup (graph.modules.map fun m => (m.name, m)) graph.entry "scoped entry" = .ok node

def checkScopedRoot (graph : ScopedProgram) (wires : Nat) (banks : List Resource) :
    Except String (ScopedRoot graph wires banks) :=
  match last : graph.modules.getLast? with
  | none => .error "The scoped graph has no root"
  | some node =>
    if name : node.name = graph.entry then
      if width : node.publicWires = wires then
        if entryWidth : graph.entryWires = wires then
          if resources : node.banks = banks then
            if decodedNode : lookup (graph.modules.map fun m => (m.name, m)) graph.entry "scoped entry" =
                .ok node then
              .ok ⟨graph.modules.dropLast, node, (List.dropLast_append_getLast? node (by simp [last])).symm,
                name, width, entryWidth, resources, decodedNode⟩
            else .error "The snapshot decoder selects a different entry"
          else .error "The scoped root has unexpected ordered banks"
        else .error "The scoped graph records an unexpected entry width"
      else .error "The scoped root has an unexpected width"
    else .error "The scoped root is not the final definition"

noncomputable def ScopedRoot.known {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) : ScopedEnvironment :=
  scopedEnvironment root.previous [] unboundScopedOracle

theorem ScopedRoot.lookup_root {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) (label : String) :
    lookup (scopedEnvironment graph.modules [] unboundScopedOracle) graph.entry label =
      .ok ⟨root.node.publicWires, root.node.banks, root.node.interpret root.known⟩ := by
  rw [root.order, ← root.name]
  exact lookup_scoped_definition root.previous [] root.node (by simp) label

theorem ScopedRoot.lookup_banks {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) {child : ScopedDefinition}
    (lookup : lookup (scopedEnvironment graph.modules [] unboundScopedOracle)
      graph.entry "scoped callee" = .ok child) : child.banks = banks := by
  rw [root.lookup_root] at lookup
  cases lookup
  exact root.resources

theorem ScopedRoot.matrix_of_node {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) (snapshot : Snapshot)
    {u : WireMatrix root.node.publicWires} (computed : root.node.interpret root.known snapshot = .ok u) :
    graph.matrixWith snapshot = .ok ((root.width.trans root.entryWidth.symm) ▸ u) := by
  have width := root.width.trans root.entryWidth.symm
  unfold ScopedProgram.matrixWith
  dsimp only
  rw [root.lookup_root]
  simp [width, computed, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ScopedRoot.source_matrix_of_node {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) {source : Program}
    (resolved : source.resolveScoped = .ok graph) (snapshot : Snapshot)
    {u : WireMatrix root.node.publicWires} (computed : root.node.interpret root.known snapshot = .ok u) :
    source.scopedMatrix snapshot = .ok ⟨wires, root.width ▸ u⟩ := by
  cases root.entryWidth
  exact Program.scopedMatrix_of_resolved resolved (root.matrix_of_node snapshot computed)

theorem ScopedRoot.source_matrix_of_public {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) {source : Program}
    (resolved : source.resolveScoped = .ok graph) (snapshot : Snapshot) {u : WireMatrix wires}
    (computed : root.node.interpret root.known snapshot = .ok (root.width.symm ▸ u)) :
    source.scopedMatrix snapshot = .ok ⟨wires, u⟩ := by
  have evaluated := root.source_matrix_of_node resolved snapshot computed
  have cancel {a b : Nat} (eq : a = b) (matrix : WireMatrix b) :
      (eq ▸ (eq.symm ▸ matrix) : WireMatrix b) = matrix := by
    subst b
    rfl
  rw [cancel root.width u] at evaluated
  exact evaluated

theorem ScopedRoot.source_matrix_of_module {graph : ScopedProgram} {wires : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) {source : Program}
    (resolved : source.resolveScoped = .ok graph) (snapshot : Snapshot)
    {m : ScopedModule} (node : root.node = m) (width : m.publicWires = wires)
    {u : WireMatrix m.publicWires} (computed : m.interpret root.known snapshot = .ok u) :
    source.scopedMatrix snapshot = .ok ⟨wires, width ▸ u⟩ := by
  subst m
  exact root.source_matrix_of_node resolved snapshot computed

theorem ScopedRoot.place {original : List ScopedModule} {graph : ScopedProgram}
    {wires width : Nat} {banks : List Resource}
    (root : ScopedRoot graph wires banks) (projection : ClosedProjection original graph.modules)
    (snapshot forwarded : Snapshot) (site : CallSite) (name : site.name = graph.entry)
    (view : View width wires)
    (layout : View.ofWires width wires site.arguments.flatten = .ok view)
    (forwarding : snapshot.forward banks site.banks = .ok forwarded)
    {source : Program} (resolved : source.resolveScoped = .ok graph) {u : WireMatrix wires}
    (evaluated : source.scopedMatrix forwarded = .ok ⟨wires, u⟩) :
    (scopedEnvironment original [] unboundScopedOracle).atCall width snapshot site =
      .ok (view.placeMatrix u) := by
  cases root.entryWidth
  have member : root.node ∈ graph.modules := by rw [root.order]; simp
  apply projection.place snapshot forwarded site width name ⟨root.node, member, root.name⟩ view layout
  · intro definition selected
    rw [name] at selected
    rw [root.lookup_banks selected]
    exact forwarding
  · exact Program.resolved_of_scopedMatrix resolved evaluated

theorem ScopedModule.interpret_unitary {m : ScopedModule} {known : ScopedEnvironment}
    {memory : Snapshot} {u : WireMatrix m.publicWires}
    (interpreted : m.interpret known memory = .ok u) :
    u ∈ Matrix.unitaryGroup (Reg m.publicWires) ℂ := by
  unfold ScopedModule.interpret at interpreted
  cases evaluated : m.bodyMatrix memory (known.atCall m.width memory) with
  | error reason => simp [evaluated, Bind.bind, Except.bind] at interpreted
  | ok matrix =>
    simp only [evaluated, Bind.bind, Except.bind] at interpreted
    split at interpreted
    · rename_i accepted
      cases interpreted
      exact m.publicMatrix_unitary accepted.1 accepted.2
    · cases interpreted

private def UnitaryDefinitions (known : ScopedEnvironment) : Prop :=
  ∀ name child, lookup known name "scoped callee" = .ok child →
    ∀ memory (u : WireMatrix child.publicWires), child.apply memory = .ok u →
      u ∈ Matrix.unitaryGroup (Reg child.publicWires) ℂ

private theorem unitaryDefinitions_scoped (modules : List ScopedModule) :
    UnitaryDefinitions (scopedEnvironment modules [] unboundScopedOracle) := by
  suffices step : ∀ known, UnitaryDefinitions known →
      UnitaryDefinitions (scopedEnvironment modules [] unboundScopedOracle known) by
    apply step []
    intro name child missing
    cases missing
  induction modules with
  | nil => exact fun _ accepted => accepted
  | cons m rest ih =>
    intro known accepted
    apply ih
    intro name child found memory matrix computed
    change lookup (known.extend m [] unboundScopedOracle) name "scoped callee" = .ok child at found
    by_cases matchName : (name == m.name) = true
    · simp [ScopedEnvironment.extend, lookup, List.lookup, matchName] at found
      cases found
      exact ScopedModule.interpret_unitary computed
    · have different : (name == m.name) = false := Bool.eq_false_iff.mpr matchName
      simp [ScopedEnvironment.extend, lookup, List.lookup, different] at found
      exact accepted name child found memory matrix computed

/-- Every successful bound call induces a unitary on the caller's physical frame. -/
theorem scopedCall_unitary {modules : List ScopedModule} {wires : Nat} {snapshot : Snapshot}
    {site : CallSite} {u : WireMatrix wires}
    (computed : (scopedEnvironment modules [] unboundScopedOracle).atCall wires snapshot site = .ok u) :
    u ∈ Matrix.unitaryGroup (Reg wires) ℂ := by
  let known := scopedEnvironment modules [] unboundScopedOracle
  unfold ScopedEnvironment.atCall at computed
  cases found : lookup known site.name "scoped callee" with
  | error reason => simp [known, found, Bind.bind, Except.bind] at computed
  | ok child =>
    change (do
      let d ← lookup known site.name "scoped callee"
      let v ← View.ofWires wires d.publicWires site.arguments.flatten
      let bank ← snapshot.forward d.banks site.banks
      let body ← d.apply bank
      return v.placeMatrix body) = .ok u at computed
    simp only [found, Bind.bind, Except.bind] at computed
    cases selected : View.ofWires wires child.publicWires site.arguments.flatten with
    | error reason => simp [selected] at computed
    | ok view =>
      cases routed : snapshot.forward child.banks site.banks with
      | error reason => simp [selected, routed] at computed
      | ok bank =>
        cases evaluated : child.apply bank with
        | error reason => simp [selected, routed, evaluated] at computed
        | ok body =>
          simp only [selected, routed, evaluated, Pure.pure, Except.pure, Except.ok.injEq] at computed
          rw [← computed]
          exact view.placeMatrix_unitary (unitaryDefinitions_scoped modules _ child found _ _ evaluated)

end OracqVerify.RIR
