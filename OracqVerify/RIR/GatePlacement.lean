module

public import OracqVerify.RIR.GateAction
public import OracqVerify.RIR.ScopedPlacement

/-! A structural certificate for relocating gate words onto distinct ordered wires. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

deriving instance DecidableEq for GateAction

private theorem outside_and_inside {n k : Nat} (view : View n k) (r c : Reg n) :
    r = c ↔ (∀ i : {i : Fin n // i ∉ Set.range view}, r i.val = c i.val) ∧
      r ∘ view = c ∘ view := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, rfl⟩
  · rintro ⟨outside, inside⟩
    funext i
    by_cases h : i ∈ Set.range view
    · obtain ⟨j, rfl⟩ := h
      exact congrFun inside j
    · exact outside ⟨i, h⟩

private theorem place_atWire {n k : Nat} (view : View n k) (wire : Fin k)
    (u : Matrix Bool Bool ℂ) :
    view.placeMatrix (atWire wire u) = atWire (view wire) u := by
  ext r c
  rw [view.placeMatrix_apply]
  unfold atWire
  have split :
      (∀ i : Fin n, i ≠ view wire → r i = c i) ↔
      (∀ i : {i : Fin n // i ∉ Set.range view}, r i.val = c i.val) ∧
      (∀ i : Fin k, i ≠ wire → r (view i) = c (view i)) := by
    constructor
    · intro h
      exact ⟨fun i => h i.val (fun eq => i.property ⟨wire, eq.symm⟩),
        fun i different => h (view i) (fun eq => different (view.injective eq))⟩
    · rintro ⟨outside, inside⟩ i different
      by_cases h : i ∈ Set.range view
      · obtain ⟨j, rfl⟩ := h
        exact inside j (fun eq => different (congrArg view eq))
      · exact outside ⟨i, h⟩
  simp only [split, Function.comp_apply, ite_and]

theorem View.placeMatrix_one {n k : Nat} (view : View n k) :
    view.placeMatrix 1 = 1 := by
  ext r c
  simp only [view.placeMatrix_apply, Matrix.one_apply, outside_and_inside view r c, ite_and]

private theorem place_phase {n k : Nat} (view : View n k) (phase : ℂ) :
    view.placeMatrix (diagonal (fun _ => phase)) = diagonal (fun _ => phase) := by
  ext r c
  rw [view.placeMatrix_apply]
  simp only [Matrix.diagonal_apply, outside_and_inside view r c, ite_and]

private theorem place_control {n k : Nat} (view : View n k) (active : Reg k → Prop)
    (u : WireMatrix k) :
    view.placeMatrix (controlledMatrix active u) =
      controlledMatrix (fun row => active (row ∘ view)) (view.placeMatrix u) := by
  ext r c
  rw [view.placeMatrix_apply]
  by_cases holds : active (r ∘ view) ∧ active (c ∘ view)
  · simp [controlledMatrix, holds, view.placeMatrix_apply]
  · simp only [controlledMatrix, ite_eq_right holds, Matrix.one_apply,
      outside_and_inside view r c, ite_and]

/-- Relocate a local gate and all its guard coordinates together. -/
def GateAction.place {n k : Nat} (view : View n k) : GateAction k → GateAction n
  | .unary gate wire inv => .unary gate (view wire) inv
  | .phase angle inv => .phase angle inv
  | .control guard value body => .control (guard.trans view) value (body.place view)

theorem GateAction.place_matrix {n k : Nat} (view : View n k) (step : GateAction k) :
    (step.place view).matrix = view.placeMatrix step.matrix := by
  induction step with
  | unary => exact (place_atWire ..).symm
  | phase => exact (place_phase ..).symm
  | control guard value body ih =>
    simp only [place, matrix, ih, place_control]
    rfl

def GateAction.inverse {n : Nat} : GateAction n → GateAction n
  | .unary gate wire inv => .unary gate wire (!inv)
  | .phase angle inv => .phase angle (!inv)
  | .control guard value body => .control guard value body.inverse

theorem GateAction.inverse_matrix {n : Nat} (step : GateAction n) :
    step.inverse.matrix = step.matrixᴴ := by
  induction step with
  | unary gate wire inv =>
    change atWire wire (if !inv then (unaryMatrix gate)ᴴ else unaryMatrix gate) =
      (atWire wire (if inv then (unaryMatrix gate)ᴴ else unaryMatrix gate))ᴴ
    rw [atWire_adjoint]
    cases inv <;> simp
  | phase angle inv =>
    rw [inverse, matrix, matrix, diagonal_conjTranspose]
    cases inv <;> simp [GateCoefficients.exact]
  | control guard value body ih =>
    simp [inverse, matrix, ih, controlledMatrix_adjoint]

theorem GateAction.placed_word {n k : Nat} (view : View n k) (word : List (GateAction k)) :
    wordMatrix ((word.map (place view)).map matrix) =
      view.placeMatrix (wordMatrix (word.map matrix)) := by
  induction word with
  | nil => simp [wordMatrix, view.placeMatrix_one]
  | cons step tail ih =>
    simp only [List.map_cons, wordMatrix, ih, place_matrix, view.placeMatrix_mul]

/-- Serialization can use any decimal spelling for zero. Only obvious
identities are removed by the structural gate-word comparison. -/
def GateAction.isZeroRotation {n : Nat} : GateAction n → Bool
  | .unary (.ry angle) _ _ | .phase angle _ => angle.mantissa == 0
  | .control _ _ body => body.isZeroRotation
  | _ => false

private theorem atWire_identity {n : Nat} (wire : Fin n) : atWire wire 1 = 1 := by
  ext row col
  by_cases same : row = col
  · subst col
    simp [atWire]
  · have different : ¬ (∀ i, i ≠ wire → row i = col i) ∨ row wire ≠ col wire := by
      by_cases h : ∀ i, i ≠ wire → row i = col i
      · right
        intro bit
        apply same
        funext i
        by_cases eq : i = wire
        · simpa [eq] using bit
        · exact h i eq
      · exact Or.inl h
    rcases different with outside | bit <;> simp [atWire, *]

theorem GateAction.zero_matrix {n : Nat} (step : GateAction n)
    (isZero : step.isZeroRotation = true) : step.matrix = 1 := by
  induction step with
  | unary gate wire inv =>
    cases gate with
    | h | x | z => contradiction
    | ry angle =>
      have mantissa : angle.mantissa = 0 := eq_of_beq isZero
      have θ : angleValue angle = 0 := by simp [angleValue, mantissa]
      have gateZero : rotationY 0 = 1 := by
        ext r c
        cases r <;> cases c <;> simp [rotationY]
      change atWire wire (if inv then (unaryMatrix (.ry angle))ᴴ else unaryMatrix (.ry angle)) = 1
      simp only [unaryMatrix, θ, gateZero, conjTranspose_one, ite_self, atWire_identity]
  | phase angle inv =>
    have mantissa : angle.mantissa = 0 := eq_of_beq isZero
    have θ : angleValue angle = 0 := by simp [angleValue, mantissa]
    cases inv <;> simp [matrix, GateCoefficients.exact, θ]
  | control guard value body ih =>
    rw [matrix, ih isZero, controlledMatrix_one]

theorem GateAction.word_without_zero {n : Nat} (word : List (GateAction n)) :
    wordMatrix ((word.filter fun step => !step.isZeroRotation).map matrix) =
      wordMatrix (word.map matrix) := by
  induction word with
  | nil => rfl
  | cons step rest ih =>
    cases zero : step.isZeroRotation
    · simp [zero, wordMatrix, ih]
    · simp [zero, wordMatrix, ih, step.zero_matrix zero]

end OracqVerify.RIR
