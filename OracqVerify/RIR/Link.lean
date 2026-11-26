module

public import OracqVerify.RIR.Semantics

/-! Semantic substitution for resolved oracle calls, including controlled and adjoint calls. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix
open scoped Matrix

/-- The name and ordered quantum and bank actuals of a resolved open call. -/
structure CallSite where
  name : String
  arguments : List (List Nat)
  banks : List Resource
  deriving DecidableEq

abbrev Oracle (width : Nat) := CallSite → Except String (WireMatrix width)
abbrev Implementations := CallSite → List ResolvedInstruction

/-- Evaluate a resolved word relative to a specification for each open call site. -/
noncomputable def ResolvedInstruction.matrixWith (width : Nat) (snapshot : Snapshot)
    (oracle : Oracle width) : ResolvedInstruction → Except String (WireMatrix width)
  | .query name arguments banks => oracle ⟨name, arguments, banks⟩
  | .controlled guard body => do
    let view ← View.ofWires width guard.wires.length guard.wires
    let u ← body.matrixWith width snapshot oracle
    return controlledMatrix (matchesGuard view guard.value) u
  | .adjoint body => do
    let u ← body.matrixWith width snapshot oracle
    return uᴴ
  | atom => atom.matrix width snapshot

/-- Inline an implementation already expressed in the entry coordinates of its call site.
Adjunction reverses the inlined word and adjoints each instruction. -/
def ResolvedInstruction.inline (implementations : Implementations) :
    ResolvedInstruction → List ResolvedInstruction
  | .query name arguments banks => implementations ⟨name, arguments, banks⟩
  | .controlled guard body => (body.inline implementations).map (.controlled guard)
  | .adjoint body => (body.inline implementations).reverse.map .adjoint
  | atom => [atom]

/-- Evidence for one resolved call context. The control constructor requires every inlined
instruction to preserve the guard sectors. Its query constructor checks the complete matrix
of the implementation at the physical argument and bank coordinates. -/
inductive LinkStep (width : Nat) (snapshot : Snapshot) (oracle : Oracle width)
    (implementations : Implementations) : ResolvedInstruction → List (WireMatrix width) → Prop
  | unary (gate : UnaryGate) (wires : List Nat) {u : WireMatrix width}
      (matrix : (ResolvedInstruction.unary gate wires).matrix width snapshot = .ok u) :
      LinkStep width snapshot oracle implementations (.unary gate wires) [u]
  | phase (angle : Lean.JsonNumber) :
      LinkStep width snapshot oracle implementations (.gphase angle)
        [globalPhase width (angleValue angle)]
  | xor (source target : List Nat) {u : WireMatrix width}
      (matrix : (ResolvedInstruction.xor source target).matrix width snapshot = .ok u) :
      LinkStep width snapshot oracle implementations (.xor source target) [u]
  | addConst (wires : List Nat) (amount : Nat) {u : WireMatrix width}
      (matrix : (ResolvedInstruction.addConst wires amount).matrix width snapshot = .ok u) :
      LinkStep width snapshot oracle implementations (.addConst wires amount) [u]
  | load (bank : Resource) (address data : List Nat) {u : WireMatrix width}
      (matrix : (ResolvedInstruction.load bank address data).matrix width snapshot = .ok u) :
      LinkStep width snapshot oracle implementations (.load bank address data) [u]
  | query (site : CallSite) (word : List (WireMatrix width))
      (concrete : (implementations site).mapM (ResolvedInstruction.matrix width snapshot) = .ok word)
      (abstract : oracle site = .ok (wordMatrix word)) :
      LinkStep width snapshot oracle implementations (.query site.name site.arguments site.banks) word
  | control (guard : Guard) {body : ResolvedInstruction} {word : List (WireMatrix width)}
      (view : View width guard.wires.length)
      (decode : View.ofWires width guard.wires.length guard.wires = .ok view)
      (hbody : LinkStep width snapshot oracle implementations body word)
      (preserves : ∀ u ∈ word, Preserves (matchesGuard view guard.value) u) :
      LinkStep width snapshot oracle implementations (.controlled guard body)
        (word.map (controlledMatrix (matchesGuard view guard.value)))
  | adjoint {body : ResolvedInstruction} {word : List (WireMatrix width)}
      (hbody : LinkStep width snapshot oracle implementations body word) :
      LinkStep width snapshot oracle implementations (.adjoint body) (word.reverse.map conjTranspose)

private theorem mapM_except_lift {A B C D : Type} (f : A → Except String B)
    (g : C → Except String D) (wrap : A → C) (transform : B → D)
    (lift : ∀ x y, f x = .ok y → g (wrap x) = .ok (transform y))
    {xs : List A} {ys : List B} (result : xs.mapM f = .ok ys) :
    (xs.map wrap).mapM g = .ok (ys.map transform) := by
  induction xs generalizing ys with
  | nil => cases result; rfl
  | cons x tail ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at result
    split at result
    · contradiction
    · rename_i y hy
      split at result
      · contradiction
      · rename_i rest hr
        cases result
        simp [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, lift x y hy, ih hr]

private theorem mapM_except_reverse {A B : Type} (f : A → Except String B)
    {xs : List A} {ys : List B} (result : xs.mapM f = .ok ys) :
    xs.reverse.mapM f = .ok ys.reverse := by
  induction xs generalizing ys with
  | nil => cases result; rfl
  | cons x tail ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at result
    split at result
    · contradiction
    · rename_i y hy
      split at result
      · contradiction
      · rename_i rest hr
        cases result
        simp [List.reverse_cons, List.mapM_append, List.mapM_cons, Bind.bind, Except.bind,
          Pure.pure, Except.pure, hy, ih hr]

variable {width : Nat} {snapshot : Snapshot} {oracle : Oracle width}
  {implementations : Implementations}

/-- A certified contextual substitution denotes the same complete matrix as the abstract call. -/
theorem LinkStep.sound {step : ResolvedInstruction} {word : List (WireMatrix width)}
    (link : LinkStep width snapshot oracle implementations step word) :
    (step.inline implementations).mapM (ResolvedInstruction.matrix width snapshot) = .ok word ∧
    step.matrixWith width snapshot oracle = .ok (wordMatrix word) := by
  induction link with
  | unary _ _ h | xor _ _ h | addConst _ _ h | load _ _ _ h =>
    simp [ResolvedInstruction.inline, ResolvedInstruction.matrixWith, h, wordMatrix,
      List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | phase angle => simp [ResolvedInstruction.inline, ResolvedInstruction.matrixWith,
      ResolvedInstruction.matrix, wordMatrix]
  | query site word concrete spec => exact ⟨concrete, spec⟩
  | control guard view decode _ preserves ih =>
    constructor
    · exact mapM_except_lift (ResolvedInstruction.matrix width snapshot)
        (ResolvedInstruction.matrix width snapshot) (.controlled guard)
        (controlledMatrix (matchesGuard view guard.value))
        (fun x y h => by simp [ResolvedInstruction.matrix, decode, h, Bind.bind,
          Except.bind, Pure.pure, Except.pure]) ih.1
    · rw [wordMatrix_controlled _ _ preserves]
      simp [ResolvedInstruction.matrixWith, decode, ih.2, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  | adjoint _ ih =>
    constructor
    · exact mapM_except_lift (ResolvedInstruction.matrix width snapshot)
        (ResolvedInstruction.matrix width snapshot) .adjoint conjTranspose
        (fun x y h => by simp [ResolvedInstruction.matrix, h, Bind.bind,
          Except.bind, Pure.pure, Except.pure]) (mapM_except_reverse _ ih.1)
    · rw [wordMatrix_reverse_adjoint]
      simp [ResolvedInstruction.matrixWith, ih.2, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A certificate for each step composes into a certificate for the entire resolved program. -/
theorem linkWord_sound (steps : List ResolvedInstruction)
    (checked : ∀ step ∈ steps, ∃ word, LinkStep width snapshot oracle implementations step word) :
    (do let gates ← (steps.flatMap (ResolvedInstruction.inline implementations)).mapM
          (ResolvedInstruction.matrix width snapshot)
        pure (wordMatrix gates)) =
      (do let gates ← steps.mapM (ResolvedInstruction.matrixWith width snapshot oracle)
          pure (wordMatrix gates)) := by
  suffices h : ∃ concrete abstract,
      (steps.flatMap (ResolvedInstruction.inline implementations)).mapM
        (ResolvedInstruction.matrix width snapshot) = .ok concrete ∧
      steps.mapM (ResolvedInstruction.matrixWith width snapshot oracle) = .ok abstract ∧
      wordMatrix concrete = wordMatrix abstract by
    obtain ⟨_, _, concrete, abstract, same⟩ := h
    simp [concrete, abstract, same, Bind.bind, Except.bind, Pure.pure, Except.pure]
  induction steps with
  | nil => exact ⟨[], [], rfl, rfl, rfl⟩
  | cons head tail ih =>
    obtain ⟨word, link⟩ := checked head (by simp)
    obtain ⟨concrete, abstract, hc, ha, he⟩ :=
      ih (fun step hm => checked step (List.mem_cons_of_mem _ hm))
    refine ⟨word ++ concrete, wordMatrix word :: abstract, ?_, ?_, ?_⟩
    · simp [List.flatMap_cons, List.mapM_append, link.sound.1, hc, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
    · simp [List.mapM_cons, link.sound.2, ha, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rw [wordMatrix_append, wordMatrix, he]

end OracqVerify.RIR
