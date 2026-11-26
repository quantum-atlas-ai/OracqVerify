module

public import OracqVerify.RIR.ScopedSemantics
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Place a closed public interface on the ordered actual wires of a scope. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Qatlib.Foundations.PureStateMath Matrix
open scoped Matrix Kronecker

abbrev Spectators {n k : Nat} (view : View n k) := {i : Fin n // i ∉ Set.range view} → Bool

noncomputable def View.splitBasis {n k : Nat} (view : View n k) :
    Reg n ≃ Reg k × Spectators view := by
  classical
  let e := (Equiv.sumCongr (Equiv.ofInjective view view.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range view))
  exact (e.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow ..)

@[simp] theorem View.splitBasis_public {n k : Nat} (view : View n k) (state : Reg n) :
    (view.splitBasis state).1 = state ∘ view := rfl

@[simp] theorem View.splitBasis_spectators {n k : Nat} (view : View n k) (state : Reg n) :
    (view.splitBasis state).2 = fun i => state i.val := rfl

noncomputable def View.placeMatrix {n k : Nat} (view : View n k) (u : WireMatrix k) :
    WireMatrix n := by
  classical
  exact Matrix.reindex view.splitBasis.symm view.splitBasis.symm
    (u ⊗ₖ (1 : Matrix (Spectators view) (Spectators view) ℂ))

theorem View.placeMatrix_apply {n k : Nat} (view : View n k) (u : WireMatrix k)
    (row col : Reg n) :
    view.placeMatrix u row col =
      if ∀ i : {i : Fin n // i ∉ Set.range view}, row i.val = col i.val
      then u (row ∘ view) (col ∘ view)
      else 0 := by
  classical
  have same : ((fun i : {i : Fin n // i ∉ Set.range view} => row i.val) =
      (fun i => col i.val)) ↔ ∀ i : {i : Fin n // i ∉ Set.range view}, row i.val = col i.val :=
    ⟨fun equality bit => congrFun equality bit, funext⟩
  simp [View.placeMatrix, Matrix.reindex_apply, Matrix.kroneckerMap,
    Matrix.of_apply, Matrix.one_apply, same]

theorem View.placeMatrix_mul {n k : Nat} (view : View n k) (u v : WireMatrix k) :
    view.placeMatrix (u * v) = view.placeMatrix u * view.placeMatrix v := by
  classical
  let I : Matrix (Spectators view) (Spectators view) ℂ := 1
  have one : I * I = I := by simp [I]
  change Matrix.reindexAlgEquiv ℂ ℂ view.splitBasis.symm ((u * v) ⊗ₖ I) =
    Matrix.reindexAlgEquiv ℂ ℂ view.splitBasis.symm (u ⊗ₖ I) *
      Matrix.reindexAlgEquiv ℂ ℂ view.splitBasis.symm (v ⊗ₖ I)
  rw [← one, mul_kronecker_mul, map_mul, one]

theorem View.placeMatrix_adjoint {n k : Nat} (view : View n k) (u : WireMatrix k) :
    view.placeMatrix uᴴ = (view.placeMatrix u)ᴴ := by
  classical
  simp [View.placeMatrix, Matrix.conjTranspose_kronecker]

theorem View.placeMatrix_unitary {n k : Nat} (view : View n k) {u : WireMatrix k}
    (unitary : u ∈ Matrix.unitaryGroup (Reg k) ℂ) :
    view.placeMatrix u ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  have product : u * uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp unitary
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← view.placeMatrix_adjoint,
    ← view.placeMatrix_mul, product]
  classical
  simp [View.placeMatrix]

theorem View.placeMatrix_preserves_guard {n k w : Nat} (view : View n k) (guard : View n w)
    (apart : ∀ i j, view i ≠ guard j) (value : Nat) (u : WireMatrix k) :
    Preserves (matchesGuard guard value) (view.placeMatrix u) := by
  classical
  intro row col separates
  rw [view.placeMatrix_apply]
  apply ite_eq_right
  intro same
  have sameGuard (j : Fin w) : row (guard j) = col (guard j) := by
    apply same ⟨guard j, ?_⟩
    rintro ⟨i, e⟩
    exact apart i j e
  apply separates
  simp only [matchesGuard, sameGuard]

end OracqVerify.RIR
