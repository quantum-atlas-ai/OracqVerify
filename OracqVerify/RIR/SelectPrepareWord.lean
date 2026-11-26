module

public import OracqVerify.RIR.GatePlacement
public import OracqVerify.RIR.SelectPrepare

/-! Verify SELECT/PREPARE using structure and component gate words. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix

/-- The selector and branch wires are ordered independently and partition the public frame. -/
structure SelectLayout (n s k : Nat) where
  selector : View n s
  branch : View n k
  apart : ∀ i j, selector i ≠ branch j
  covers : ∀ i, i ∈ Set.range selector ∨ i ∈ Set.range branch

namespace SelectLayout

noncomputable def basis {n s k : Nat} (layout : SelectLayout n s k) : Reg n ≃ Reg s × Reg k := by
  classical
  apply Equiv.ofBijective (fun state => (state ∘ layout.selector, state ∘ layout.branch))
  constructor
  · intro x y same
    funext i
    rcases layout.covers i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact congrFun (congrArg Prod.fst same) j
    · exact congrFun (congrArg Prod.snd same) j
  · rintro ⟨label, data⟩
    let state : Reg n := fun i =>
      if l : i ∈ Set.range layout.selector then label (Classical.choose l)
      else data (Classical.choose ((layout.covers i).resolve_left l))
    refine ⟨state, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩
    · have hit : layout.selector j ∈ Set.range layout.selector := ⟨j, rfl⟩
      have selected : Classical.choose hit = j := layout.selector.injective (Classical.choose_spec hit)
      change state (layout.selector j) = label j
      simp only [state, dite_eq_left hit, selected]
    · have miss : layout.branch j ∉ Set.range layout.selector := fun ⟨i, h⟩ => layout.apart i j h
      have inBranch : ∃ i, layout.branch i = layout.branch j :=
        (layout.covers (layout.branch j)).resolve_left miss
      have selected : Classical.choose inBranch = j :=
        layout.branch.injective (Classical.choose_spec inBranch)
      change state (layout.branch j) = data j
      simp only [state, dite_eq_right miss, selected]

noncomputable def lift {n s k : Nat} (layout : SelectLayout n s k) :
    Matrix (Reg s × Reg k) (Reg s × Reg k) ℂ ≃ₐ[ℂ] WireMatrix n :=
  Matrix.reindexAlgEquiv ℂ ℂ layout.basis.symm

theorem lift_apply {n s k : Nat} (layout : SelectLayout n s k)
    (U : Matrix (Reg s × Reg k) (Reg s × Reg k) ℂ) (r c : Reg n) :
    layout.lift U r c = U (r ∘ layout.selector, r ∘ layout.branch)
      (c ∘ layout.selector, c ∘ layout.branch) := rfl

private theorem spectator_selector {n s k : Nat} (layout : SelectLayout n s k) (r c : Reg n) :
    (∀ i : {i : Fin n // i ∉ Set.range layout.branch}, r i.val = c i.val) ↔
      r ∘ layout.selector = c ∘ layout.selector := by
  constructor
  · intro equal
    funext i
    exact equal ⟨layout.selector i, fun ⟨j, h⟩ => layout.apart i j h.symm⟩
  · intro equal ⟨i, outside⟩
    obtain ⟨j, rfl⟩ := (layout.covers i).resolve_right outside
    exact congrFun equal j

private theorem spectator_branch {n s k : Nat} (layout : SelectLayout n s k) (r c : Reg n) :
    (∀ i : {i : Fin n // i ∉ Set.range layout.selector}, r i.val = c i.val) ↔
      r ∘ layout.branch = c ∘ layout.branch := by
  constructor
  · intro equal
    funext i
    exact equal ⟨layout.branch i, fun ⟨j, h⟩ => layout.apart j i h⟩
  · intro equal ⟨i, outside⟩
    obtain ⟨j, rfl⟩ := (layout.covers i).resolve_left outside
    exact congrFun equal j

theorem prepare_place {n s k : Nat} (layout : SelectLayout n s k) (P : WireMatrix s) :
    layout.selector.placeMatrix P = layout.lift (prepareRegister (I := Reg k) P) := by
  classical
  ext r c
  rw [layout.selector.placeMatrix_apply]
  simp only [layout.spectator_branch, lift_apply, prepareRegister, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]

theorem branch_place {n s k : Nat} (layout : SelectLayout n s k) (U : WireMatrix k) :
    layout.branch.placeMatrix U = layout.lift (select (fun _ => U)) := by
  classical
  ext r c
  rw [layout.branch.placeMatrix_apply]
  simp only [layout.spectator_selector, lift_apply, select, Matrix.of_apply]

def label {s : Nat} (value : Nat) : Reg s := fun i => value.testBit i.val

theorem guarded_place {n s k : Nat} (layout : SelectLayout n s k) (value : Nat)
    (U : WireMatrix k) :
    controlledMatrix (matchesGuard layout.selector value) (layout.branch.placeMatrix U) =
      layout.lift (selectorCall (label value) U) := by
  classical
  ext r c
  have active (x : Reg n) : matchesGuard layout.selector value x ↔
      x ∘ layout.selector = label value :=
    ⟨funext, fun e i => congrFun e i⟩
  have eq : (r ∘ layout.selector = c ∘ layout.selector ∧
       r ∘ layout.branch = c ∘ layout.branch) ↔ r = c := by
    constructor
    · rintro ⟨h₁, h₂⟩
      apply layout.basis.injective
      exact Prod.ext h₁ h₂
    · rintro rfl
      exact ⟨rfl, rfl⟩
  by_cases both : r ∘ layout.selector = label value ∧ c ∘ layout.selector = label value
  · simp only [branch_place, lift_apply, controlledMatrix, active, selectorCall, ite_eq_left both]
  · simp only [branch_place, lift_apply, controlledMatrix, active, selectorCall, ite_eq_right both,
      Matrix.one_apply, Prod.mk.injEq, eq]

theorem lift_adjoint {n s k : Nat} (layout : SelectLayout n s k)
    (U : Matrix (Reg s × Reg k) (Reg s × Reg k) ℂ) :
    (layout.lift U)ᴴ = layout.lift Uᴴ := rfl

theorem lift_word {n s k : Nat} (layout : SelectLayout n s k)
    (word : List (Matrix (Reg s × Reg k) (Reg s × Reg k) ℂ)) :
    wordMatrix (word.map layout.lift) = layout.lift (wordMatrix word) := by
  induction word with
  | nil => simp [wordMatrix]
  | cons step tail ih => simp [wordMatrix, ih, map_mul]

/-- Construct the expected flat gate word from independent component traces. -/
def word {n s k : Nat} (layout : SelectLayout n s k)
    (prepare : List (GateAction s)) (order : List Nat) (branch : Nat → List (GateAction k)) :
    List (GateAction n) :=
  let prepared := prepare.map (GateAction.place layout.selector)
  let selected := order.flatMap fun j =>
    (branch j).map fun step => .control layout.selector j (step.place layout.branch)
  prepared ++ selected ++ prepared.reverse.map GateAction.inverse

private theorem guarded_word {n s k : Nat} (layout : SelectLayout n s k) (j : Nat)
    (steps : List (GateAction k)) :
    wordMatrix ((steps.map fun step => GateAction.control layout.selector j
      (step.place layout.branch)).map GateAction.matrix) =
      layout.lift (selectorCall (label j) (wordMatrix (steps.map GateAction.matrix))) := by
  simp only [List.map_map, Function.comp_def, GateAction.matrix, GateAction.place_matrix]
  rw [show (steps.map fun step =>
      controlledMatrix (matchesGuard layout.selector j) (layout.branch.placeMatrix step.matrix)) =
      ((steps.map (GateAction.place layout.branch)).map GateAction.matrix).map
        (controlledMatrix (matchesGuard layout.selector j)) by
          simp [Function.comp_def, GateAction.place_matrix]]
  rw [wordMatrix_controlled _ _ (by
    intro gate occurs
    simp only [List.map_map, List.mem_map] at occurs
    obtain ⟨step, _, rfl⟩ := occurs
    rw [Function.comp_apply, GateAction.place_matrix]
    exact layout.branch.placeMatrix_preserves_guard layout.selector
      (fun a b h => layout.apart b a h.symm) j step.matrix)]
  rw [GateAction.placed_word, guarded_place]

theorem word_matrix {n s k : Nat} (layout : SelectLayout n s k) (prepare : List (GateAction s))
    (order : List Nat) (branch : Reg s → List (GateAction k))
    (unique : (order.map (label (s := s))).Nodup)
    (complete : ∀ j : Reg s, j ∈ order.map (label (s := s))) :
    let P := prepareRegister (I := Reg k) (wordMatrix (prepare.map GateAction.matrix))
    wordMatrix ((layout.word prepare order (fun j => branch (label j))).map GateAction.matrix) =
      layout.lift (Pᴴ * select (fun j => wordMatrix ((branch j).map GateAction.matrix)) * P) := by
  dsimp only
  let P := prepareRegister (I := Reg k) (wordMatrix (prepare.map GateAction.matrix))
  let U := fun j => wordMatrix ((branch j).map GateAction.matrix)
  let placed := prepare.map (GateAction.place layout.selector)
  have prepared : wordMatrix (placed.map GateAction.matrix) = layout.lift P := by
    dsimp only [placed, P]
    rw [GateAction.placed_word, prepare_place]
  have unprepared :
      wordMatrix ((placed.reverse.map GateAction.inverse).map GateAction.matrix) =
        (layout.lift P)ᴴ := by
    have gates : (placed.reverse.map GateAction.inverse).map GateAction.matrix =
        (placed.reverse.map GateAction.matrix).map Matrix.conjTranspose := by
      simp only [List.map_map, Function.comp_def, GateAction.inverse_matrix]
    rw [gates, List.map_reverse, wordMatrix_reverse_adjoint, prepared]
  have selected (js : List Nat) :
      wordMatrix ((js.flatMap fun j => (branch (label j)).map fun step =>
        GateAction.control layout.selector j (step.place layout.branch)).map GateAction.matrix) =
        layout.lift (wordMatrix ((js.map (label (s := s))).map fun j => selectorCall j (U j))) := by
    induction js with
    | nil => simp [wordMatrix]
    | cons j rest ih =>
      rw [List.flatMap_cons, List.map_append, wordMatrix_append, ih, guarded_word]
      simp [wordMatrix, U, map_mul]
  unfold word
  change wordMatrix ((placed ++ _ ++ placed.reverse.map GateAction.inverse).map GateAction.matrix) = _
  simp only [List.map_append, wordMatrix_append, unprepared, prepared, selected, lift_adjoint]
  rw [selectorCalls_word _ unique, show
    (fun j => if j ∈ order.map (label (s := s)) then U j else 1) = U by
      funext j
      exact ite_eq_left (complete j)]
  simp only [map_mul, Matrix.mul_assoc, P, U]

def tagged {s k : Nat} (zero : Reg s) : Reg k ↪ Reg s × Reg k :=
  ⟨fun state => (zero, state), fun _ _ h => congrArg Prod.snd h⟩

/-- The full success frame is the zero-selector tag of the branch frame. -/
theorem compress_lift {n s k : Nat} {I : Type} [Fintype I] [DecidableEq I]
    (layout : SelectLayout n s k) (U : Matrix (Reg s × Reg k) (Reg s × Reg k) ℂ)
    (e : I ↪ Reg k) (zero : Reg s) :
    let input := basisFrame ((e.trans (tagged zero)).trans layout.basis.symm.toEmbedding)
    compress input (layout.lift U) input =
      compress (selectPrepareFrame zero (basisFrame e)) U (selectPrepareFrame zero (basisFrame e)) := by
  dsimp only
  have frame : selectPrepareFrame zero (basisFrame e) = basisFrame (e.trans (tagged zero)) := by
    ext row col
    rw [selectPrepareFrame, Matrix.mul_apply, Finset.sum_eq_single (e col)]
    · have pair : (e.trans (tagged zero)) col = (zero, e col) := rfl
      by_cases data : row.2 = e col <;> by_cases label : row.1 = zero <;>
        simp [basisFrame, prepareLift, Ket, pair, Prod.ext_iff, data, label, eq_comm]
      exact Ne.symm label
    · intro b _ different
      simp [basisFrame, different]
    · simp
  rw [frame]
  ext r c
  rw [basisFrame_compress, basisFrame_compress]
  change U (layout.basis (layout.basis.symm (zero, e r)))
      (layout.basis (layout.basis.symm (zero, e c))) = U (zero, e r) (zero, e c)
  simp

end SelectLayout
end OracqVerify.RIR
