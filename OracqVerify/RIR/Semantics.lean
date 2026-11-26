module

public import OracqVerify.RIR.ModularAddition

/-! Exact complex matrix semantics for the closed fragment used by the first LCHS artifact. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath
open scoped Classical Matrix

abbrev WireMatrix (wireCount : Nat) := Matrix (Reg wireCount) (Reg wireCount) ℂ

/-- A serialized angle denotes the exact decimal in the RIR, in radians. -/
noncomputable def angleValue (angle : Lean.JsonNumber) : ℝ :=
  (angle.mantissa : ℝ) / (10 : ℝ) ^ angle.exponent

/-- The real Y-axis rotation in the computational basis, with rows indexed by outputs. -/
noncomputable def rotationY (angle : ℝ) : Matrix Bool Bool ℂ :=
  fun row col =>
    if row = col then (Real.cos (angle / 2) : ℂ)
    else if row then (Real.sin (angle / 2) : ℂ) else -(Real.sin (angle / 2) : ℂ)

theorem rotationY_adjoint (angle : ℝ) :
    (rotationY angle)ᴴ = rotationY (-angle) := by
  ext x y
  cases x <;> cases y <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, rotationY, Matrix.conjTranspose_apply,
      neg_div, Real.sin_neg, Real.cos_neg]

noncomputable def unaryMatrix : UnaryGate → Matrix Bool Bool ℂ
  | .h => Hadamard
  | .x => PauliX
  | .z => PauliZ
  | .ry angle => rotationY (angleValue angle)

/-- A single-wire gate acts as the identity on every spectator bit. -/
noncomputable def atWire {wireCount : Nat} (wire : Fin wireCount) (gate : Matrix Bool Bool ℂ) :
    WireMatrix wireCount :=
  fun row col => if ∀ i : Fin wireCount, i ≠ wire → row i = col i then gate (row wire) (col wire)
    else 0

/-- Multiply all amplitudes by the same exact complex phase. -/
noncomputable def globalPhase (wireCount : Nat) (angle : ℝ) : WireMatrix wireCount :=
  Matrix.diagonal fun _ => Complex.exp ((angle : ℂ) * Complex.I)

/-- Predicate on the ordered view, with its first wire tested against bit zero. -/
def matchesGuard {wireCount width : Nat} (view : View wireCount width) (value : Nat)
    (state : Reg wireCount) : Prop :=
  ∀ i : Fin width, state (view i) = value.testBit i.val

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Coherent control puts the active operation in its block and identity in the other block. -/
noncomputable def controlledMatrix (active : I → Prop) (gate : Matrix I I ℂ) : Matrix I I ℂ :=
  fun row col => if active row ∧ active col then gate row col else (1 : Matrix I I ℂ) row col

/-- An operation preserves a control predicate when its matrix connects no opposite sectors. -/
def Preserves (active : I → Prop) (gate : Matrix I I ℂ) : Prop :=
  ∀ row col, ¬ (active row ↔ active col) → gate row col = 0

omit [Fintype I] in
theorem Preserves.one (active : I → Prop) : Preserves active (1 : Matrix I I ℂ) := by
  intro row col h
  have hne : row ≠ col := fun heq => h (heq ▸ Iff.rfl)
  simp [hne]

omit [DecidableEq I] in
theorem Preserves.mul {active : I → Prop} {u v : Matrix I I ℂ}
    (hU : Preserves active u) (hV : Preserves active v) : Preserves active (u * v) := by
  intro row col h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : active row ↔ active k
  · rw [hV k col (fun hkc => h (hk.trans hkc)), mul_zero]
  · rw [hU row k hk, zero_mul]

omit [Fintype I] [DecidableEq I] in
theorem Preserves.adjoint {active : I → Prop} {gate : Matrix I I ℂ}
    (h : Preserves active gate) : Preserves active gateᴴ := by
  intro row col different
  have opposite : ¬ (active col ↔ active row) := fun same => different same.symm
  simp [Matrix.conjTranspose_apply, h col row opposite]

omit [Fintype I] in
theorem Preserves.controlled {active : I → Prop} {gate : Matrix I I ℂ}
    (h : Preserves active gate) (control : I → Prop) :
    Preserves active (controlledMatrix control gate) := by
  intro row col different
  unfold controlledMatrix
  split
  · exact h row col different
  · exact Preserves.one active row col different

omit [Fintype I] in
theorem controlledMatrix_one (active : I → Prop) :
    controlledMatrix active (1 : Matrix I I ℂ) = 1 := by
  ext row col
  simp [controlledMatrix]

omit [Fintype I] in
/-- Distinct nested control tests combine by conjunction. -/
theorem controlledMatrix_nested (outer inner : I → Prop) (gate : Matrix I I ℂ) :
    controlledMatrix outer (controlledMatrix inner gate) =
      controlledMatrix (fun state => outer state ∧ inner state) gate := by
  ext row col
  have conditions : ((outer row ∧ inner row) ∧ (outer col ∧ inner col)) ↔
      (outer row ∧ outer col) ∧ (inner row ∧ inner col) := by tauto
  simp only [controlledMatrix, conditions]
  by_cases ho : outer row ∧ outer col <;> by_cases hi : inner row ∧ inner col <;>
    simp [ho, hi]

omit [Fintype I] in
theorem controlledMatrix_adjoint (active : I → Prop) (gate : Matrix I I ℂ) :
    (controlledMatrix active gate)ᴴ = controlledMatrix active gateᴴ := by
  ext row col
  by_cases hr : active row <;> by_cases hc : active col <;>
    simp [controlledMatrix, Matrix.conjTranspose_apply, Matrix.one_apply, hr, hc, eq_comm]

/-- Control can be distributed over a product when the first matrix preserves the guard sectors. -/
theorem controlledMatrix_mul (active : I → Prop) (u v : Matrix I I ℂ)
    (hU : Preserves active u) :
    controlledMatrix active u * controlledMatrix active v = controlledMatrix active (u * v) := by
  ext row col
  by_cases hr : active row
  · by_cases hc : active col
    · simp only [controlledMatrix, hr, hc, and_self, ite_true, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : active k
      · simp [hk]
      · rw [hU row k (by intro h; exact hk (h.mp hr))]
        simp [hk, Matrix.one_apply, show row ≠ k from fun h => hk (h ▸ hr)]
    · have hcol (k : I) : controlledMatrix active v k col = (1 : Matrix I I ℂ) k col := by
        simp [controlledMatrix, hc]
      calc
        _ = (controlledMatrix active u * (1 : Matrix I I ℂ)) row col := by
          simp only [Matrix.mul_apply, hcol]
        _ = _ := by simp [controlledMatrix, hc]
  · have hrow (k : I) : controlledMatrix active u row k = (1 : Matrix I I ℂ) row k := by
      simp [controlledMatrix, hr]
    calc
      _ = ((1 : Matrix I I ℂ) * controlledMatrix active v) row col := by
        simp only [Matrix.mul_apply, hrow]
      _ = _ := by simp [controlledMatrix, hr]

/-- A guarded global phase changes just the enabled basis amplitudes. -/
theorem controlled_globalPhase_diagonal {wireCount : Nat} (active : Reg wireCount → Prop)
    (angle : ℝ) (state : Reg wireCount) :
    controlledMatrix active (globalPhase wireCount angle) state state =
      if active state then Complex.exp ((angle : ℂ) * Complex.I) else 1 := by
  simp [controlledMatrix, globalPhase]

theorem controlled_globalPhase_offDiagonal {wireCount : Nat} (active : Reg wireCount → Prop)
    (angle : ℝ) {row col : Reg wireCount} (different : row ≠ col) :
    controlledMatrix active (globalPhase wireCount angle) row col = 0 := by
  simp [controlledMatrix, globalPhase, different]

/-- In superposition, only the active amplitudes acquire the global phase. -/
theorem controlled_globalPhase_apply {wireCount : Nat} (active : Reg wireCount → Prop)
    (angle : ℝ) (state : QState (Reg wireCount)) (row : Reg wireCount) :
    ApplyGate (controlledMatrix active (globalPhase wireCount angle)) state row =
      (if active row then Complex.exp ((angle : ℂ) * Complex.I) else 1) * state row := by
  have diagonal : controlledMatrix active (globalPhase wireCount angle) =
      Matrix.diagonal (fun input =>
        if active input then Complex.exp ((angle : ℂ) * Complex.I) else 1) := by
    ext input output
    by_cases same : input = output
    · subst output
      simpa using controlled_globalPhase_diagonal active angle input
    · rw [controlled_globalPhase_offDiagonal active angle same, Matrix.diagonal_apply_ne _ same]
  rw [diagonal, ApplyGate, Matrix.mulVec_diagonal]

/-- A gate on a wire disjoint from the control cannot mix that control's sectors. -/
theorem atWire_preserves_guard {wireCount width : Nat} (wire : Fin wireCount)
    (gate : Matrix Bool Bool ℂ) (guard : View wireCount width) (value : Nat)
    (disjoint : ∀ i : Fin width, guard i ≠ wire) :
    Preserves (matchesGuard guard value) (atWire wire gate) := by
  intro row col different
  have notSpectators : ¬ ∀ i : Fin wireCount, i ≠ wire → row i = col i := by
    intro spectators
    apply different
    constructor
    · intro h i
      rw [← spectators (guard i) (disjoint i)]
      exact h i
    · intro h i
      rw [spectators (guard i) (disjoint i)]
      exact h i
  simp [atWire, notSpectators]

theorem globalPhase_preserves {wireCount : Nat} (control : Reg wireCount → Prop) (angle : ℝ) :
    Preserves control (globalPhase wireCount angle) := by
  intro row col h
  have hne : row ≠ col := fun heq => h (heq ▸ Iff.rfl)
  simp [globalPhase, hne]

private theorem permutation_preserves_guard {wireCount width : Nat} (f : Reg wireCount → Reg wireCount)
    (guard : View wireCount width) (value : Nat)
    (preserved : ∀ state i, f state (guard i) = state (guard i)) :
    Preserves (matchesGuard guard value) (permMatrix f) := by
  intro row col different
  have hne : row ≠ f col := by
    intro same
    apply different
    have unchanged (i : Fin width) : row (guard i) = col (guard i) := same.symm ▸ preserved col i
    constructor
    · intro h i
      rw [← unchanged i]
      exact h i
    · intro h i
      rw [unchanged i]
      exact h i
  simp [permMatrix, hne]

/-- A load preserves a guard when the data wires are disjoint from the guard view. -/
theorem loadAt_preserves_guard {wireCount a d width : Nat} (address : View wireCount a)
    (data : View wireCount d) (bank : ReadOnlyQRAM.Bank a d) (guard : View wireCount width)
    (value : Nat) (disjoint : DisjointViews guard data) :
    Preserves (matchesGuard guard value) (permMatrix (loadAtBasis address data bank)) := by
  apply permutation_preserves_guard
  intro state i
  apply loadAt_other
  rintro ⟨j, hj⟩
  exact disjoint i j hj.symm

/-- A modular addition preserves every guard on spectator wires. -/
theorem addAt_preserves_guard {wireCount w width : Nat} (target : View wireCount w)
    (amount : BitVec w) (guard : View wireCount width) (value : Nat)
    (disjoint : DisjointViews guard target) :
    Preserves (matchesGuard guard value) (permMatrix (addAtBasis target amount)) := by
  apply permutation_preserves_guard
  intro state i
  apply addAtBasis_other
  rintro ⟨j, hj⟩
  exact disjoint i j hj.symm

/-- Compose a word in execution order, so the last matrix acts on the left. -/
noncomputable def wordMatrix : List (Matrix I I ℂ) → Matrix I I ℂ
  | [] => 1
  | gate :: tail => wordMatrix tail * gate

theorem wordMatrix_append (first second : List (Matrix I I ℂ)) :
    wordMatrix (first ++ second) = wordMatrix second * wordMatrix first := by
  induction first with
  | nil => simp [wordMatrix]
  | cons gate rest ih => simp [wordMatrix, ih, mul_assoc]

theorem wordMatrix_preserves (active : I → Prop) (word : List (Matrix I I ℂ))
    (h : ∀ gate ∈ word, Preserves active gate) : Preserves active (wordMatrix word) := by
  induction word with
  | nil => exact Preserves.one active
  | cons gate rest ih =>
    exact (ih (fun u hu => h u (List.mem_cons_of_mem _ hu))).mul (h gate (by simp))

/-- Closing a whole control block agrees with controlling each guard-preserving operation. -/
theorem wordMatrix_controlled (active : I → Prop) (word : List (Matrix I I ℂ))
    (h : ∀ gate ∈ word, Preserves active gate) :
    wordMatrix (word.map (controlledMatrix active)) = controlledMatrix active (wordMatrix word) := by
  induction word with
  | nil => simp [wordMatrix, controlledMatrix_one]
  | cons gate rest ih =>
    have hRest (u : Matrix I I ℂ) (hu : u ∈ rest) : Preserves active u :=
      h u (List.mem_cons_of_mem _ hu)
    simp only [List.map_cons, wordMatrix, ih hRest]
    exact controlledMatrix_mul active _ _ (wordMatrix_preserves active rest hRest)

/-- Reversing the word and adjointing each gate gives the adjoint of its execution. -/
theorem wordMatrix_reverse_adjoint (word : List (Matrix I I ℂ)) :
    wordMatrix (word.reverse.map Matrix.conjTranspose) = (wordMatrix word)ᴴ := by
  induction word with
  | nil => simp [wordMatrix]
  | cons gate rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton, wordMatrix_append,
      wordMatrix, one_mul, ih, Matrix.conjTranspose_mul]

/-- Word-wise XOR is the fixed coherent read with the address word as its contents. -/
noncomputable def xorMatrix (wireCount : Nat) (source target : List Nat) :
    Except String (WireMatrix wireCount) := do
  let a ← View.ofWires wireCount source.length source
  let d ← View.ofWires wireCount source.length target
  unless ∀ i j, a i ≠ d j do throw "XOR views overlap"
  return permMatrix (loadAtBasis a d id)

/-- Interpret the resolved operations, using entry wire coordinates and a separate QRAM snapshot. -/
noncomputable def ResolvedInstruction.matrix (wireCount : Nat) (snapshot : Snapshot) :
    ResolvedInstruction → Except String (WireMatrix wireCount)
  | .unary gate wires => do
    let view ← View.ofWires wireCount wires.length wires
    return wordMatrix ((List.finRange wires.length).map fun i => atWire (view i) (unaryMatrix gate))
  | .gphase angle => .ok (globalPhase wireCount (angleValue angle))
  | .xor source target => xorMatrix wireCount source target
  | .addConst wires amount => addConstMatrix wireCount wires amount
  | .load bank address data => (ResolvedInstruction.load bank address data).loadMatrix wireCount snapshot
  | .query name .. => .error s!"The slot {name} needs a concrete binding for matrix semantics"
  | .controlled guard instruction => do
    let view ← View.ofWires wireCount guard.wires.length guard.wires
    let gate ← instruction.matrix wireCount snapshot
    return controlledMatrix (matchesGuard view guard.value) gate
  | .adjoint instruction => do
    let gate ← instruction.matrix wireCount snapshot
    return gateᴴ

/-- Compose the exact matrix denotation of a closed, resolved program. -/
noncomputable def ResolvedProgram.matrix (program : ResolvedProgram) (snapshot : Snapshot) :
    Except String (WireMatrix program.wireCount) := do
  let gates ← program.instructions.mapM (ResolvedInstruction.matrix program.wireCount snapshot)
  return wordMatrix gates

/-- Resolve a closed RIR program and interpret it on its entry wire basis. -/
noncomputable def Program.matrix (program : Program) (snapshot : Snapshot) :
    Except String (Σ wireCount : Nat, WireMatrix wireCount) := do
  let resolved ← program.resolve
  return ⟨resolved.wireCount, ← resolved.matrix snapshot⟩

end OracqVerify.RIR
