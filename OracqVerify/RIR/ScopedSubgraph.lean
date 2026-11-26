module

public import OracqVerify.RIR.ScopedLink
public import OracqVerify.RIR.SnapshotImage

/-! Restrict a closed scoped graph without changing the meanings of its retained modules. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

def ResolvedInstruction.callees : ResolvedInstruction → List String
  | .query name _ _ => [name]
  | .controlled _ step | .adjoint step => step.callees
  | _ => []

def ScopedModule.callees (m : ScopedModule) : List String :=
  (m.body.getD []).flatMap ResolvedInstruction.callees

/-- Closing a step depends only on the entries that its own syntax queries. -/
theorem ResolvedInstruction.matrixWith_congr_on {n : Nat} (step : ResolvedInstruction)
    (snap : Snapshot) (first second : Oracle n)
    (same : ∀ site, site.name ∈ step.callees → first site = second site) :
    step.matrixWith n snap first = step.matrixWith n snap second := by
  induction step with
  | query name args banks => exact same ⟨name, args, banks⟩ (by simp [callees])
  | controlled guard body ih =>
    have related := ih (fun call member => same call member)
    simp [ResolvedInstruction.matrixWith, related]
  | adjoint body ih =>
    have related := ih (fun call member => same call member)
    simp [ResolvedInstruction.matrixWith, related]
  | unary | gphase | xor | addConst | load => rfl

private theorem mapM_eq_of_agreement {A B : Type} (f g : A → Except String B)
    (steps : List A) (same : ∀ step ∈ steps, f step = g step) :
    steps.mapM f = steps.mapM g := by
  induction steps with
  | nil => rfl
  | cons head rest ih =>
    rw [List.mapM_cons, List.mapM_cons, same head (by simp)]
    rw [ih (fun step found => same step (List.mem_cons_of_mem _ found))]

/-- Equality on the callees is enough to preserve a module's clean public result. -/
theorem ScopedModule.interpret_congr_on (m : ScopedModule)
    (first second : ScopedEnvironment)
    (same : ∀ name ∈ m.callees, lookup first name "scoped callee" =
      lookup second name "scoped callee") :
    m.interpret first = m.interpret second := by
  funext snap
  have equation : m.bodyMatrix snap (first.atCall m.width snap) =
      m.bodyMatrix snap (second.atCall m.width snap) := by
    unfold ScopedModule.bodyMatrix
    cases decoded : m.body with
    | none => rfl
    | some steps =>
      change (steps.mapM (ResolvedInstruction.matrixWith m.width snap (first.atCall m.width snap))).map
        wordMatrix = (steps.mapM (ResolvedInstruction.matrixWith m.width snap (second.atCall m.width snap))).map
        wordMatrix
      congr 1
      apply mapM_eq_of_agreement
      intro step present
      apply step.matrixWith_congr_on
      intro site called
      have active : site.name ∈ m.callees :=
        List.mem_flatMap.mpr ⟨step, by simpa [decoded] using present, called⟩
      unfold ScopedEnvironment.atCall
      rw [same _ active]
  unfold ScopedModule.interpret
  rw [equation]

/-- A filtered set of names is closed if it retains every call of each retained module. -/
def CalleeClosed (keep : String → Bool) (modules : List ScopedModule) : Prop :=
  ∀ m ∈ modules, keep m.name = true → ∀ name ∈ m.callees, keep name = true

def checkCalleeClosed (keep : String → Bool) (modules : List ScopedModule) : Bool :=
  modules.all fun m => !keep m.name || m.callees.all keep

theorem checkCalleeClosed_sound {keep : String → Bool} {modules : List ScopedModule}
    (checked : checkCalleeClosed keep modules = true) : CalleeClosed keep modules := by
  intro m present retained
  have fact := List.all_eq_true.mp checked m present
  simp only [retained, Bool.not_true, Bool.false_or] at fact
  exact List.all_eq_true.mp fact

/-- An extracted subgraph has the same definitions and order as filtering the
original postorder graph, and retains all calls made from those definitions. -/
structure ClosedProjection (original projected : List ScopedModule) where
  keep : String → Bool
  closed : CalleeClosed keep original
  retained : projected = original.filter fun m => keep m.name

def checkClosedProjection (original projected : List ScopedModule) :
    Except String (ClosedProjection original projected) :=
  let names := projected.map ScopedModule.name
  let keep := names.contains
  if checked : checkCalleeClosed keep original = true then
    if retained : projected = original.filter fun m => keep m.name then
      .ok ⟨keep, checkCalleeClosed_sound checked, retained⟩
    else .error "Extracted definitions differ from the ordered scoped graph"
  else .error "Extracted scoped graph is missing a callee"

def SameDefinitions (keep : String → Bool) (first second : ScopedEnvironment) : Prop :=
  ∀ name, keep name = true →
    lookup first name "scoped callee" = lookup second name "scoped callee"

private theorem lookup_extended (known : ScopedEnvironment) (m : ScopedModule)
    (name : String) :
    lookup (known.extend m [] unboundScopedOracle) name "scoped callee" =
      if name == m.name then .ok ⟨m.publicWires, m.banks, m.interpret known⟩
      else lookup known name "scoped callee" := by
  cases hit : name == m.name <;>
    simp [ScopedEnvironment.extend, lookup, List.lookup, hit]

/-- Taking a callee-closed subgraph commutes with interpreting every selected module.
The proof keeps lexical snapshot functions, so it also preserves bank forwarding. -/
theorem scopedEnvironment_filter (keep : String → Bool) (modules : List ScopedModule)
    (closed : CalleeClosed keep modules) {first second : ScopedEnvironment}
    (same : SameDefinitions keep first second) :
    SameDefinitions keep
      (scopedEnvironment modules [] unboundScopedOracle first)
      (scopedEnvironment (modules.filter fun m => keep m.name) [] unboundScopedOracle second) := by
  induction modules generalizing first second with
  | nil => simpa [scopedEnvironment] using same
  | cons m rest ih =>
    have smaller : CalleeClosed keep rest :=
      fun sub present => closed sub (List.mem_cons_of_mem _ present)
    by_cases live : keep m.name = true
    · simp only [List.filter_cons, live, ite_true, scopedEnvironment, List.foldl_cons]
      change SameDefinitions keep
        (scopedEnvironment rest [] unboundScopedOracle (first.extend m [] unboundScopedOracle))
        (scopedEnvironment (rest.filter fun m => keep m.name) [] unboundScopedOracle
          (second.extend m [] unboundScopedOracle))
      apply ih smaller
      intro name kept
      have meaning := m.interpret_congr_on first second
        (fun callee called => same callee (closed m (by simp) live callee called))
      rw [lookup_extended, lookup_extended, meaning, same name kept]
    · have dropped : keep m.name = false := Bool.eq_false_iff.mpr live
      simp only [List.filter_cons, dropped, Bool.false_eq_true, ite_false, scopedEnvironment, List.foldl_cons]
      change SameDefinitions keep
        (scopedEnvironment rest [] unboundScopedOracle (first.extend m [] unboundScopedOracle))
        (scopedEnvironment (rest.filter fun m => keep m.name) [] unboundScopedOracle second)
      apply ih smaller
      intro name kept
      have distinct : name ≠ m.name := fun eq => live (eq ▸ kept)
      have miss : (name == m.name) = false := Bool.eq_false_iff.mpr (fun equal => distinct (eq_of_beq equal))
      rw [lookup_extended, miss]
      exact same name kept


/-- Changing the diagnostic label of a lookup does not affect an equality of lookups. -/
theorem lookup_same_at {A : Type} {first second : List (String × A)}
    {name kind : String} (same : lookup first name kind = lookup second name kind) (label : String) :
    lookup first name label = lookup second name label := by
  have sameOption : first.lookup name = second.lookup name := by
    cases left : first.lookup name <;> cases right : second.lookup name <;>
      simp only [lookup, left, right, Except.ok.injEq, reduceCtorEq] at same <;>
      first | rfl | exact congrArg some same
  unfold lookup
  rw [sameOption]

theorem scopedMatrix_filter (program : ScopedProgram) (keep : String → Bool) (snapshot : Snapshot)
    (closed : CalleeClosed keep program.modules) (entry : keep program.entry = true) :
    { program with modules := program.modules.filter fun m => keep m.name }.matrixWith snapshot =
      program.matrixWith snapshot := by
  have same := scopedEnvironment_filter keep program.modules closed
    (first := []) (second := []) (fun _ _ => rfl) program.entry entry
  change lookup (scopedEnvironment _ [] unboundScopedOracle []) program.entry "scoped callee" =
    lookup (scopedEnvironment _ [] unboundScopedOracle []) program.entry "scoped callee" at same
  have found := lookup_same_at same "scoped entry"
  unfold ScopedProgram.matrixWith
  dsimp only
  rw [found]

private theorem place_in_frame {n width : Nat} (child : ScopedDefinition)
    (forwarded : Snapshot) (wires : List Nat) (view : View n width)
    (sameWidth : child.publicWires = width)
    (layout : View.ofWires n width wires = .ok view)
    {u : WireMatrix width} (eval : (do
      let body ← child.apply forwarded
      return sameWidth ▸ body) = .ok u) :
    (do
      let actual ← View.ofWires n child.publicWires wires
      let body ← child.apply forwarded
      return actual.placeMatrix body) = .ok (view.placeMatrix u) := by
  subst width
  rw [layout]
  cases evaluated : child.apply forwarded <;>
    simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A callee-closed projection yields the same placed call when the actual bank
snapshot has already been forwarded to the selected definition's lexical frame. -/
theorem ScopedProgram.place_from_closed_projection (program : ScopedProgram)
    (keep : String → Bool) (snapshot forwarded : Snapshot) (site : CallSite) (n : Nat)
    (closed : CalleeClosed keep program.modules) (entry : keep site.name = true)
    (name : site.name = program.entry)
    (view : View n program.entryWires)
    (layout : View.ofWires n program.entryWires site.arguments.flatten = .ok view)
    (selectedBanks : ∀ d, lookup
      (scopedEnvironment (program.modules.filter fun m => keep m.name) [] unboundScopedOracle)
        site.name "scoped callee" = .ok d → snapshot.forward d.banks site.banks = .ok forwarded)
    {u : WireMatrix program.entryWires}
    (denoted : {program with modules := program.modules.filter fun m => keep m.name}.matrixWith
      forwarded = .ok u) :
    (scopedEnvironment program.modules [] unboundScopedOracle).atCall n snapshot site =
      .ok (view.placeMatrix u) := by
  let full := scopedEnvironment program.modules [] unboundScopedOracle
  let small := scopedEnvironment (program.modules.filter fun m => keep m.name) [] unboundScopedOracle
  have lookupEq : lookup full site.name "scoped callee" = lookup small site.name "scoped callee" :=
    scopedEnvironment_filter keep program.modules closed (first := []) (second := [])
      (by intro _ _; rfl) site.name entry
  have interpreted : (do
      let d ← lookup small site.name "scoped entry"
      if h : d.publicWires = program.entryWires then
        let body ← d.apply forwarded
        return h ▸ body
      else throw "Scoped entry width mismatch") = .ok u := by
    rw [name]
    exact denoted
  cases chosen : lookup small site.name "scoped callee" with
  | error reason =>
    have miss : small.lookup site.name = none := by
      unfold lookup at chosen
      split at chosen
      · cases chosen
      · assumption
    simp [lookup, miss, Bind.bind, Except.bind] at interpreted
  | ok child =>
    have found : lookup small site.name "scoped entry" = .ok child := by
      have belongs : small.lookup site.name = some child := by
        unfold lookup at chosen
        split at chosen
        · cases chosen
          assumption
        · cases chosen
      simp [lookup, belongs]
    have childForward := selectedBanks child chosen
    simp only [found, Bind.bind, Except.bind] at interpreted
    split at interpreted
    · rename_i sameWidth
      change (do
        let d ← lookup full site.name "scoped callee"
        let actual ← View.ofWires n d.publicWires site.arguments.flatten
        let memory ← snapshot.forward d.banks site.banks
        let body ← d.apply memory
        return actual.placeMatrix body) = _
      rw [lookupEq, chosen]
      simp only [Bind.bind, Except.bind]
      cases actualLayout : View.ofWires n child.publicWires site.arguments.flatten with
      | error reason =>
        have placed := place_in_frame child forwarded site.arguments.flatten view sameWidth layout interpreted
        rw [actualLayout] at placed
        cases placed
      | ok actual =>
        rw [childForward]
        have placed := place_in_frame child forwarded site.arguments.flatten view sameWidth layout interpreted
        rw [actualLayout] at placed
        exact placed
    · cases interpreted

/-- Use the public matrix of the checked extracted program at a call in the
complete graph. The caller supplies the view and exact forwarded snapshot. -/
theorem ClosedProjection.place {original : List ScopedModule} {extracted : ScopedProgram}
    (projection : ClosedProjection original extracted.modules)
    (snapshot forwarded : Snapshot) (site : CallSite) (width : Nat)
    (entry : site.name = extracted.entry)
    (present : ∃ m ∈ extracted.modules, m.name = extracted.entry)
    (view : View width extracted.entryWires)
    (layout : View.ofWires width extracted.entryWires site.arguments.flatten = .ok view)
    (banks : ∀ d, lookup (scopedEnvironment extracted.modules [] unboundScopedOracle)
      site.name "scoped callee" = .ok d → snapshot.forward d.banks site.banks = .ok forwarded)
    {u : WireMatrix extracted.entryWires} (denoted : extracted.matrixWith forwarded = .ok u) :
    (scopedEnvironment original [] unboundScopedOracle).atCall width snapshot site =
      .ok (view.placeMatrix u) := by
  obtain ⟨m, member, name⟩ := present
  rw [projection.retained] at member
  have selected : projection.keep site.name = true := by
    rw [entry, ← name]
    exact (List.mem_filter.mp member).2
  let complete := { extracted with modules := original }
  refine complete.place_from_closed_projection projection.keep snapshot forwarded site width
    projection.closed selected entry view layout ?_ ?_
  · intro child found
    apply banks child
    simpa only [projection.retained] using found
  · change {extracted with modules := original.filter (fun m => projection.keep m.name)}.matrixWith
        forwarded = .ok u
    rw [← projection.retained]
    exact denoted

/-- A body with no local registers exposes its ambient matrix directly. -/
theorem ScopedModule.interpret_zero_locals (name : String) (wires : Nat)
    (banks : List Resource) (body : Option (List ResolvedInstruction)) (peak : Nat)
    (control adjoint : Bool) (snapshot : Snapshot) (known : ScopedEnvironment)
    {u : WireMatrix wires} (unitary : u ∈ Matrix.unitaryGroup (Reg wires) ℂ)
    (computed : (ScopedModule.mk name wires 0 banks body peak control adjoint).bodyMatrix
      snapshot (known.atCall wires snapshot) = .ok u) :
    (ScopedModule.mk name wires 0 banks body peak control adjoint).interpret known snapshot = .ok u := by
  let m := ScopedModule.mk name wires 0 banks body peak control adjoint
  have whole (input : Reg wires) : appendZero wires 0 input = input := by
    funext i
    exact dite_eq_left i.isLt
  have clean : m.Clean u := by
    apply (m.clean_iff_zero_off_frame u).mpr
    intro row col outside
    exact (outside row (whole row).symm).elim
  rw [ScopedModule.Certificate.interpret ⟨computed, unitary, clean⟩]
  congr 1
  apply Matrix.ext
  intro row col
  change Qatlib.Concepts.Execution.WorkspaceCP.compress (basisFrame (appendZero wires 0)) u
    (basisFrame (appendZero wires 0)) row col = u row col
  rw [basisFrame_compress, whole, whole]

private theorem ResolvedInstruction.matrixWith_eq_of_noCalls (step : ResolvedInstruction)
    (wires : Nat) (snapshot : Snapshot) (oracle : Oracle wires) (closed : step.callees = []) :
    step.matrixWith wires snapshot oracle = step.matrix wires snapshot := by
  induction step with
  | query name actuals banks => simp [callees] at closed
  | controlled guard step ih =>
    simp only [callees] at closed
    simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix, ih closed]
  | adjoint step ih =>
    simp only [callees] at closed
    simp [ResolvedInstruction.matrixWith, ResolvedInstruction.matrix, ih closed]
  | unary | gphase | xor | addConst | load => rfl

/-- A resolved gate word with no subcalls has the same matrix in a flat
program and in a workspace-free lexical definition. -/
theorem ScopedModule.interpret_gateWord (name : String) (wires : Nat)
    (banks : List Resource) (steps : List ResolvedInstruction) (peak : Nat)
    (control adjoint : Bool) (snapshot : Snapshot) (known : ScopedEnvironment)
    (word : steps.all (ResolvedInstruction.isUnitaryGate wires) = true)
    {u : WireMatrix wires}
    (denoted : (ResolvedProgram.mk wires steps).matrix snapshot = .ok u) :
    (ScopedModule.mk name wires 0 banks (some steps) peak control adjoint).interpret known snapshot =
      .ok u := by
  obtain ⟨v, computed, unitary⟩ :=
    (ResolvedProgram.mk wires steps).gateMatrix_exists snapshot word
  have vu : v = u := Except.ok.inj (computed.symm.trans denoted)
  subst v
  apply interpret_zero_locals name wires banks _ peak control adjoint snapshot known unitary
  have primitive (step : ResolvedInstruction) (valid : step.isUnitaryGate wires = true) :
      step.callees = [] := by
    induction step with
    | query name args banks => simp [ResolvedInstruction.isUnitaryGate] at valid
    | controlled guard step ih =>
      exact ih (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).2).1
    | adjoint step ih => exact ih valid
    | unary | gphase | xor | addConst | load => rfl
  have same := mapM_eq_of_agreement
    (ResolvedInstruction.matrixWith wires snapshot (known.atCall wires snapshot))
    (ResolvedInstruction.matrix wires snapshot) steps
    (fun step present => step.matrixWith_eq_of_noCalls wires snapshot _
      (primitive step (List.all_eq_true.mp word step present)))
  change (do
    let gates ← steps.mapM (ResolvedInstruction.matrixWith wires snapshot (known.atCall wires snapshot))
    return wordMatrix gates) = .ok u
  rw [same]
  exact denoted

theorem View.ofWires_range (wires : Nat) :
    View.ofWires wires wires (List.range wires) = .ok (Function.Embedding.refl (Fin wires)) := by
  unfold View.ofWires
  simp [List.getElem_range, Fin.ext_iff, Pure.pure, Except.pure]
  exact Function.Embedding.ext fun _ => rfl

theorem View.placeMatrix_refl {wires : Nat} (u : WireMatrix wires) :
    View.placeMatrix (Function.Embedding.refl (Fin wires)) u = u := by
  apply Matrix.ext
  intro row col
  rw [View.placeMatrix_apply]
  have same (i : {i : Fin wires // i ∉ Set.range (Function.Embedding.refl (Fin wires))}) :
      row i.val = col i.val := (i.property ⟨i.val, rfl⟩).elim
  rw [ite_eq_left same]
  rfl

private theorem find_self_bank (banks : List Resource) (bank : Resource) :
    (banks.zip banks).find? (fun pair => decide (pair.1 = bank)) =
      if bank ∈ banks then some (bank, bank) else none := by
  induction banks with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head = bank
    · subst head
      simp
    · simp [same, Ne.symm same, ih]

/-- Forwarding unchanged bank names restricts the incoming snapshot to the
callee's interface, retaining each selected bank and its dependent type. -/
theorem Snapshot.forward_same_banks (snapshot : Snapshot) (banks : List Resource) :
    snapshot.forward banks banks =
      .ok (fun bank => if bank ∈ banks then snapshot bank else none) := by
  unfold Snapshot.forward
  simp only [eq_self, ite_true, Except.ok.injEq]
  funext bank
  rw [find_self_bank]
  by_cases member : bank ∈ banks <;> simp [member]

theorem ScopedProgram.forward_decoded_snapshot (program : ScopedProgram) (json : Lean.Json)
    {entry : ScopedModule} {snapshot : Snapshot}
    (found : lookup (program.modules.map fun m => (m.name, m)) program.entry "scoped entry" = .ok entry)
    (decoded : program.decodeSnapshot json = .ok snapshot) :
    snapshot.forward entry.banks entry.banks = .ok snapshot := by
  rw [Snapshot.forward_same_banks]
  congr 1
  funext bank
  by_cases member : bank ∈ entry.banks
  · rw [ite_eq_left member]
  · rw [ite_eq_right member, program.decodeSnapshot_outside json found decoded bank member]

/-- A later, differently named definition cannot shadow the current meaning. -/
private theorem lookup_later_definitions (name label : String) (later : List ScopedModule)
    (initial : ScopedEnvironment) (absent : name ∉ later.map ScopedModule.name) :
    lookup (scopedEnvironment later [] unboundScopedOracle initial) name label =
      lookup initial name label := by
  induction later generalizing initial with
  | nil => rfl
  | cons m later ih =>
    have apart : name ≠ m.name := fun eq => absent (by simp [eq])
    have different : (name == m.name) = false :=
      Bool.eq_false_iff.mpr fun same => apart (eq_of_beq same)
    have still : name ∉ later.map ScopedModule.name := fun found => absent (by simp [found])
    change lookup (scopedEnvironment later [] unboundScopedOracle
        (initial.extend m [] unboundScopedOracle)) name label = _
    rw [ih _ still]
    simp [ScopedEnvironment.extend, lookup, List.lookup_cons, different]

/-- In a postorder graph a definition is interpreted against the preceding
definitions, even when callers follow it in the same graph. -/
theorem lookup_scoped_definition (before after : List ScopedModule) (m : ScopedModule)
    (fresh : m.name ∉ after.map ScopedModule.name) (label : String) :
    lookup (scopedEnvironment (before ++ m :: after) [] unboundScopedOracle) m.name label =
      .ok ⟨m.publicWires, m.banks,
        m.interpret (scopedEnvironment before [] unboundScopedOracle)⟩ := by
  have split : scopedEnvironment (before ++ m :: after) [] unboundScopedOracle =
      scopedEnvironment after [] unboundScopedOracle
        ((scopedEnvironment before [] unboundScopedOracle).extend m [] unboundScopedOracle) := by
    simp only [scopedEnvironment, List.foldl_append, List.foldl_cons]
  rw [split, lookup_later_definitions _ _ _ _ fresh]
  simp [ScopedEnvironment.extend, lookup]

end OracqVerify.RIR
