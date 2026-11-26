module

public import OracqVerify.RIR.ReversibleBasis

/-! Matrix laws for executable basis permutations. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR.BasisWord

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

@[simp] theorem basis_symm_bit {n : Nat} (state : Reg n) (wire : Fin n) :
    ((basis n).symm state).readBit wire = state wire := by
  exact congrFun ((basis n).apply_symm_apply state) wire

private theorem perm_entry {n : Nat} (step : BasisWord n ≃ BasisWord n) (row col : Reg n) :
    matrix step row col = if row = perm step col then 1 else 0 := rfl

theorem matrix_refl (n : Nat) : matrix (Equiv.refl (BasisWord n)) = 1 := by
  ext row col
  simp [perm_entry, perm, Matrix.one_apply]

theorem matrix_trans {n : Nat} (first second : BasisWord n ≃ BasisWord n) :
    matrix (first.trans second) = matrix second * matrix first := by
  unfold matrix
  rw [permMatrix_comp]
  congr 1
  funext state
  simp [perm, Function.comp_def]

theorem matrix_symm {n : Nat} (step : BasisWord n ≃ BasisWord n) :
    matrix step.symm = (matrix step)ᴴ := by
  have inverse : perm step.symm = (perm step).symm := rfl
  ext row col
  rw [Matrix.conjTranspose_apply, perm_entry, perm_entry, inverse]
  have same : row = (perm step).symm col ↔ col = perm step row := by
    constructor
    · intro eq
      rw [eq, Equiv.apply_symm_apply]
    · intro eq
      rw [eq, Equiv.symm_apply_apply]
  simp [same]

theorem matrix_unitary {n : Nat} (step : BasisWord n ≃ BasisWord n) :
    matrix step ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← matrix_symm, ← matrix_trans, Equiv.symm_trans_self, matrix_refl]

theorem place_preserves {n k : Nat} (view : View n k) (action : BasisWord k ≃ BasisWord k)
    (state : BasisWord n) (wire : Fin n) (apart : ∀ i, view i ≠ wire) :
    ((place view action) state).readBit wire = state.readBit wire :=
  writeView_other _ _ _ _ apart

theorem matrix_place {n k : Nat} (view : View n k) (action : BasisWord k ≃ BasisWord k) :
    matrix (place view action) = view.placeMatrix (matrix action) := by
  classical
  ext row col
  rw [view.placeMatrix_apply, perm_entry, perm_entry]
  have readCol : readView view ((basis n).symm col) = (basis k).symm (col ∘ view) := by
    apply (basis k).injective
    funext i
    change (readView view ((basis n).symm col)).readBit i =
      ((basis k).symm (col ∘ view)).readBit i
    simp
  have selected : perm (place view action) col ∘ view = perm action (col ∘ view) := by
    funext i
    change (writeView view (action (readView view ((basis n).symm col))) _).readBit (view i) = _
    rw [writeView_bit, readCol]
    rfl
  have unchanged (i : {i : Fin n // i ∉ Set.range view}) :
      perm (place view action) col i.val = col i.val := by
    change (place view action ((basis n).symm col)).readBit i.val = col i.val
    rw [place_preserves view action _ _ (fun j h => i.property ⟨j, h⟩), basis_symm_bit]
  by_cases same : ∀ i : {i : Fin n // i ∉ Set.range view}, row i.val = col i.val
  · rw [ite_eq_left same]
    have hits : row = perm (place view action) col ↔ row ∘ view = perm action (col ∘ view) := by
      constructor
      · intro eq
        rw [eq, selected]
      · intro eq
        funext i
        by_cases inView : i ∈ Set.range view
        · obtain ⟨j, rfl⟩ := inView
          exact congrFun (eq.trans selected.symm) j
        · exact (same ⟨i, inView⟩).trans (unchanged ⟨i, inView⟩).symm
    by_cases hit : row = perm (place view action) col
    · rw [ite_eq_left hit, ite_eq_left (hits.mp hit)]
    · rw [ite_eq_right hit, ite_eq_right (fun h => hit (hits.mpr h))]
  · have missed : row ≠ perm (place view action) col :=
      fun eq => same (fun i => eq ▸ unchanged i)
    rw [ite_eq_right same, ite_eq_right missed]

theorem matrix_add {n k : Nat} (view : View n k) (amount : BitVec k) :
    matrix (add view amount) = permMatrix (addAtBasis view amount) := by
  apply congrArg (fun f : Reg n → Reg n => permMatrix f)
  funext state wire
  let input := (basis n).symm state
  have sameRead : (basis k) (readView view input) = state ∘ view := by
    funext i
    change (readView view input).readBit i = state (view i)
    simp [input]
  by_cases h : ∃ i, view i = wire
  · obtain ⟨i, rfl⟩ := h
    change (writeView view _ input).readBit (view i) = (addAtBasis view amount state ∘ view) i
    rw [writeView_bit, addAtBasis_read]
    change ((basis k).symm ((unsignedWord k).symm
      (unsignedWord k ((basis k) (readView view input)) + amount))).readBit i = _
    rw [sameRead, basis_symm_bit]
  · rw [addAtBasis_other _ _ _ _ h]
    change (writeView view _ input).readBit wire = state wire
    rw [writeView_other _ _ _ _ (fun i eq => h ⟨i, eq⟩)]
    simp [input]

theorem matrix_flip {n : Nat} (wire : Fin n) :
    matrix (flip wire) = atWire wire PauliX := by
  ext row col
  rw [perm_entry]
  have onWire : perm (flip wire) col wire = !col wire := by
    change (writeView (oneWire wire) _ _).readBit (oneWire wire 0) = !col wire
    rw [writeView_bit]
    simp [readBit, readView, oneWire, basis]
    rfl
  have other (i : Fin n) (apart : i ≠ wire) : perm (flip wire) col i = col i := by
    change (writeView (oneWire wire) _ _).readBit i = col i
    rw [writeView_other _ _ _ _ (fun j eq => apart (Eq.symm eq))]
    simp
  have full : row = perm (flip wire) col ↔
      (∀ i : Fin n, i ≠ wire → row i = col i) ∧ row wire = !col wire := by
    constructor
    · intro h
      rw [h]
      exact ⟨other, onWire⟩
    · rintro ⟨spectators, bit⟩
      funext i
      by_cases h : i = wire
      · subst i
        exact bit.trans onWire.symm
      · exact (spectators i h).trans (other i h).symm
  simp [full, atWire, PauliX, permMatrix, ite_and]

end OracqVerify.RIR.BasisWord
