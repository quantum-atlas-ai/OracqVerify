module

public import OracqVerify.RIR.GatePlacement
public import OracqVerify.RIR.QRAMRotation

/-! Conjugation by a certified fanout of controlled X gates. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

def flipAt {n : Nat} (wire : Fin n) (state : Reg n) : Reg n :=
  Function.update state wire (!state wire)

private theorem atWire_x_perm {n : Nat} (wire : Fin n) :
    atWire wire PauliX = permMatrix (flipAt wire) := by
  classical
  ext row col
  have condition : row = flipAt wire col ↔
      row wire = !col wire ∧ ∀ i : Fin n, i ≠ wire → row i = col i := by
    constructor
    · rintro rfl
      refine ⟨by simp [flipAt], fun i ne => ?_⟩
      exact Function.update_of_ne ne _ _
    · rintro ⟨hit, outside⟩
      funext i
      by_cases same : i = wire
      · subst i
        simpa [flipAt] using hit
      · simpa [flipAt, Function.update_of_ne same] using outside i same
  simp only [atWire, PauliX, permMatrix, Matrix.of_apply, condition, ite_and]
  split_ifs <;> simp_all

def cnotBasis {n : Nat} (control target : Fin n) (state : Reg n) : Reg n :=
  if state control then flipAt target state else state

theorem cnotBasis_preserves {n : Nat} {control target : Fin n} (apart : control ≠ target) (state : Reg n) :
    cnotBasis control target state control = state control := by
  unfold cnotBasis
  split
  · exact Function.update_of_ne apart _ _
  · rfl

theorem controlledX_matrix {n : Nat} (control target : Fin n) (apart : control ≠ target) :
    let guard : View n 1 := ⟨fun _ => control, fun a b _ => Subsingleton.elim a b⟩
    (GateAction.control guard 1 (.unary .x target false)).matrix =
      permMatrix (cnotBasis control target) := by
  classical
  dsimp only
  have enabled (state : Reg n) :
      matchesGuard ⟨fun _ : Fin 1 => control, fun a b _ => Subsingleton.elim a b⟩ 1 state ↔
        state control = true := by
    change (∀ i : Fin 1, state control = (1 : Nat).testBit i.val) ↔ state control = true
    rw [Fin.forall_fin_one]
    rfl
  change controlledMatrix _ (atWire target PauliX) = _
  rw [atWire_x_perm]
  ext row col
  simp only [controlledMatrix, enabled, permMatrix, of_apply]
  by_cases colActive : col control = true
  · have imageControl : flipAt target col control = true := by
      simpa [flipAt, Function.update_of_ne apart] using colActive
    by_cases rowActive : row control = true
    · simp [rowActive, colActive, cnotBasis]
    · have different : row ≠ flipAt target col := fun h => rowActive ((congrFun h control).trans imageControl)
      have unequal : row ≠ col := fun h => rowActive ((congrFun h control).trans colActive)
      simp [rowActive, colActive, cnotBasis, different, unequal]
  · simp [colActive, cnotBasis, Matrix.one_apply]

/-- Conjugation by a permutation changes the two matrix indices together. -/
theorem permMatrix_sandwich {I : Type} [Fintype I] [DecidableEq I]
    (f : I ≃ I) (u : Matrix I I ℂ) (r c : I) :
    (permMatrix f.symm * u * permMatrix f) r c = u (f r) (f c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (f c)]
  · simp only [permMatrix, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (f r)]
    · simp
    · intro k _ different
      have no : r ≠ f.symm k := fun eq => different ((Equiv.eq_symm_apply f).mp eq).symm
      simp [no]
    · simp
  · intro b _ different
    simp [permMatrix, different]
  · simp

end OracqVerify.RIR
