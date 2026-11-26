module

public import OracqVerify.RIR.ReversibleCache

/-! Compile a closed scoped graph using the same lexical calls and bank semantics as
the matrix interpreter. Bank-free definitions are compiled once and shared. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath

def emptySnapshot : Snapshot := fun _ => none

structure ReversibleDefinition where
  publicWires : Nat
  banks : List Resource
  compile (snapshot : Snapshot) : Except String (ReversibleGate publicWires)
  cached : Except String (ReversibleGate publicWires)

abbrev ReversibleEnvironment := List (String × ReversibleDefinition)

def ReversibleDefinition.forSnapshot (child : ReversibleDefinition) (snapshot : Snapshot) :
    Except String (ReversibleGate child.publicWires) :=
  if child.banks.isEmpty then child.cached else child.compile snapshot

def ReversibleEnvironment.atCall (environment : ReversibleEnvironment) (n : Nat)
    (snapshot : Snapshot) : ReversibleOracle n := fun site => do
  let child ← lookup environment site.name "scoped callee"
  let view ← View.ofWires n child.publicWires site.arguments.flatten
  let forwarded ← snapshot.forward child.banks site.banks
  let code ← child.forSnapshot forwarded
  return ReversibleGate.placed view code

abbrev ReversibleHints := String → BasisHints

def ReversibleEnvironment.extend (maxEnumeratedWires : Option Nat) (hints : ReversibleHints)
    (environment : ReversibleEnvironment) (m : ScopedModule) :
    ReversibleEnvironment :=
  let compile := fun snapshot =>
    m.compileReversible snapshot (environment.atCall m.width snapshot) maxEnumeratedWires
  let cached := if m.banks.isEmpty then
    (compile emptySnapshot).map (fun gate => gate.withHints (hints m.name))
    else .error "Definition takes banks"
  (m.name, ⟨m.publicWires, m.banks, compile, cached⟩) :: environment

def ScopedProgram.compileReversibleGate (program : ScopedProgram) (snapshot : Snapshot)
    (maxEnumeratedWires : Option Nat := none) (hints : ReversibleHints := fun _ => {}) :
    Except String (ReversibleGate program.entryWires) := do
  let environment := program.modules.foldl (ReversibleEnvironment.extend maxEnumeratedWires hints) []
  let definition ← lookup environment program.entry "scoped entry"
  if eq : definition.publicWires = program.entryWires then
    return eq ▸ (← definition.compile snapshot)
  else throw "Scoped entry width mismatch"

def ScopedProgram.compileReversible (program : ScopedProgram) (snapshot : Snapshot)
    (maxEnumeratedWires : Option Nat := none) (hints : ReversibleHints := fun _ => {}) :
    Except String (BasisWord program.entryWires ≃ BasisWord program.entryWires) :=
  (program.compileReversibleGate snapshot maxEnumeratedWires hints).map ReversibleGate.action

private inductive DefinitionSound : ReversibleDefinition → ScopedDefinition → Prop
  | mk (width : Nat) (banks : List Resource)
      (compile : Snapshot → Except String (ReversibleGate width))
      (cached : Except String (ReversibleGate width))
      (interpret : Snapshot → Except String (WireMatrix width))
      (sound : ∀ snapshot action, compile snapshot = .ok action →
        interpret snapshot = .ok action.matrix)
      (cacheSound : ∀ action, cached = .ok action →
        interpret emptySnapshot = .ok action.matrix) :
      DefinitionSound ⟨width, banks, compile, cached⟩ ⟨width, banks, interpret⟩

private abbrev EnvironmentSound (code : ReversibleEnvironment) (model : ScopedEnvironment) : Prop :=
  List.Forall₂ (fun c m => c.1 = m.1 ∧ DefinitionSound c.2 m.2) code model

private theorem lookup_sound {code : ReversibleEnvironment} {model : ScopedEnvironment}
    (cert : EnvironmentSound code model) (name kind : String) {child : ReversibleDefinition}
    (selected : lookup code name kind = .ok child) :
    ∃ sem, lookup model name kind = .ok sem ∧ DefinitionSound child sem := by
  induction cert with
  | nil => cases selected
  | cons first tail ih =>
    rename_i c m cs ms
    obtain ⟨nameEq, meaning⟩ := first
    by_cases hit : name == c.1
    · have other : name == m.1 := nameEq ▸ hit
      have same : c.2 = child := by simpa [lookup, List.lookup, hit] using selected
      exact ⟨m.2, by simp [lookup, List.lookup, other], same ▸ meaning⟩
    · have other : ¬(name == m.1) := nameEq ▸ hit
      have selectedTail : lookup cs name kind = .ok child := by
        simpa [lookup, List.lookup, hit] using selected
      obtain ⟨sem, found, certified⟩ := ih selectedTail
      exact ⟨sem, by simpa [lookup, List.lookup, other] using found, certified⟩

private theorem forward_empty {s forwarded : Snapshot} {actuals : List Resource}
    (h : s.forward [] actuals = .ok forwarded) :
    forwarded = emptySnapshot := by
  cases actuals <;> simp [Snapshot.forward] at h
  exact h.symm

private theorem atCall_sound {code : ReversibleEnvironment} {model : ScopedEnvironment}
    (cert : EnvironmentSound code model) (width : Nat) (snapshot : Snapshot) (site : CallSite)
    (gate : ReversibleGate width) (lowered : code.atCall width snapshot site = .ok gate) :
    model.atCall width snapshot site = .ok gate.matrix := by
  unfold ReversibleEnvironment.atCall at lowered
  simp only [Bind.bind, Except.bind] at lowered
  split at lowered
  · contradiction
  · rename_i child selected
    obtain ⟨sem, found, matching⟩ := lookup_sound cert _ _ selected
    unfold ScopedEnvironment.atCall
    rw [found]
    cases matching with
    | mk n banks compile cached interpret correct cacheCorrect =>
      split at lowered
      · contradiction
      · rename_i view viewOk
        split at lowered
        · contradiction
        · rename_i forwarded forwardedOk
          let definition : ReversibleDefinition := ⟨n, banks, compile, cached⟩
          cases result : definition.forSnapshot forwarded with
          | error reason => rw [result] at lowered; cases lowered
          | ok action =>
            rw [result] at lowered
            cases lowered
            have interpreted : interpret forwarded = .ok action.matrix := by
              by_cases free : banks = []
              · subst banks
                rw [forward_empty forwardedOk]
                apply cacheCorrect
                simpa [definition, ReversibleDefinition.forSnapshot] using result
              · apply correct
                simpa [definition, ReversibleDefinition.forSnapshot, List.isEmpty_iff, free] using result
            simp [viewOk, forwardedOk, interpreted, ReversibleGate.matrix, ReversibleGate.placed,
              BasisWord.matrix_place, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem extend_sound {code : ReversibleEnvironment} {model : ScopedEnvironment}
    (cert : EnvironmentSound code model) (m : ScopedModule) (maxEnumeratedWires : Option Nat)
    (hints : ReversibleHints) :
    EnvironmentSound (code.extend maxEnumeratedWires hints m) (model.extend m [] unboundScopedOracle) := by
  apply List.Forall₂.cons _ cert
  refine ⟨rfl, ?_⟩
  have correct := fun snapshot =>
    fun action => m.compileReversible_sound model snapshot (code.atCall m.width snapshot)
      (atCall_sound cert m.width snapshot) action maxEnumeratedWires
  have cachedCorrect : ∀ action,
      (if m.banks.isEmpty then
        (m.compileReversible emptySnapshot (code.atCall m.width emptySnapshot) maxEnumeratedWires).map
          (fun gate => gate.withHints (hints m.name))
        else .error "Definition takes banks") = .ok action →
      m.interpret model emptySnapshot = .ok action.matrix := by
    intro action result
    split at result
    · cases compiled : m.compileReversible emptySnapshot (code.atCall m.width emptySnapshot)
          maxEnumeratedWires with
      | error reason => rw [compiled] at result; cases result
      | ok gate =>
        rw [compiled] at result
        cases result
        rw [ReversibleGate.withHints_matrix_eq]
        exact correct emptySnapshot gate compiled
    · contradiction
  exact DefinitionSound.mk _ _ _ _ _ correct cachedCorrect

private theorem fold_sound {code : ReversibleEnvironment} {model : ScopedEnvironment}
    (cert : EnvironmentSound code model) (modules : List ScopedModule) (maxEnumeratedWires : Option Nat)
    (hints : ReversibleHints) :
    EnvironmentSound (modules.foldl (ReversibleEnvironment.extend maxEnumeratedWires hints) code)
      (scopedEnvironment modules [] unboundScopedOracle model) := by
  induction modules generalizing code model with
  | nil => exact cert
  | cons m rest ih => exact ih (extend_sound cert m maxEnumeratedWires hints)

theorem ScopedProgram.compileReversibleGate_sound (program : ScopedProgram) (snapshot : Snapshot)
    (gate : ReversibleGate program.entryWires)
    {maxEnumeratedWires : Option Nat} {hints : ReversibleHints}
    (compiled : program.compileReversibleGate snapshot maxEnumeratedWires hints = .ok gate) :
    program.matrixWith snapshot = .ok gate.matrix := by
  unfold ScopedProgram.compileReversibleGate at compiled
  dsimp only at compiled
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i child selected
    obtain ⟨sem, found, matching⟩ := lookup_sound (fold_sound List.Forall₂.nil program.modules maxEnumeratedWires hints) _ _ selected
    unfold ScopedProgram.matrixWith
    dsimp only
    rw [found]
    cases matching with
    | mk width banks compile cache interpret sound cacheSound =>
      split at compiled
      · rename_i same
        cases same
        split at compiled
        · contradiction
        · rename_i equivalent op
          cases compiled
          simp [Bind.bind, Except.bind, sound _ _ op, ReversibleGate.matrix, Pure.pure, Except.pure]
      · contradiction

theorem ScopedProgram.compileReversible_sound (program : ScopedProgram) (snapshot : Snapshot)
    (action : BasisWord program.entryWires ≃ BasisWord program.entryWires)
    {maxEnumeratedWires : Option Nat} {hints : ReversibleHints}
    (compiled : program.compileReversible snapshot maxEnumeratedWires hints = .ok action) :
    program.matrixWith snapshot = .ok (BasisWord.matrix action) := by
  unfold ScopedProgram.compileReversible at compiled
  cases result : program.compileReversibleGate snapshot maxEnumeratedWires hints with
  | error reason => rw [result] at compiled; cases compiled
  | ok gate =>
    rw [result] at compiled
    cases compiled
    exact program.compileReversibleGate_sound snapshot gate result

end OracqVerify.RIR
