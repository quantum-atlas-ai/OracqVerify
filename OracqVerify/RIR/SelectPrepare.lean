module

public import OracqVerify.RIR.ScopedPlacement
public import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary

/-! Matrix contracts for SELECT and PREPARE with a submitted coefficient preparation. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]

/-- The nonidentity branch of a single controlled call, in selector-first coordinates. -/
noncomputable def selectorCall (j : J) (u : Matrix H H ℂ) : Matrix (J × H) (J × H) ℂ :=
  controlledMatrix (fun p => p.1 = j) (select (fun _ => u))

omit [Fintype J] [Fintype H] in
theorem selectorCall_eq_select (j : J) (u : Matrix H H ℂ) :
    selectorCall j u = select (fun k => if k = j then u else 1) := by
  ext ⟨a, r⟩ ⟨b, c⟩
  by_cases same : a = b
  · subst b
    by_cases active : a = j <;> simp [selectorCall, controlledMatrix, select, active, one_apply]
  · simp [selectorCall, controlledMatrix, select, same, one_apply]

/-- Split an ordered branch view from its complement, with the selector first. -/
noncomputable def View.selectorBasis {n k : Nat} (branch : View n k) :
    Reg n ≃ Spectators branch × Reg k :=
  branch.splitBasis.trans (Equiv.prodComm _ _)

/-- A placed call with a guard on the complete complement of the branch view
is a single sector of SELECT, even for a noncontiguous, reordered branch view. -/
theorem View.placeMatrix_selectorCall {n k : Nat} (branch : View n k)
    (label : Spectators branch) (u : WireMatrix k) :
    Matrix.reindex branch.selectorBasis.symm branch.selectorBasis.symm (selectorCall label u) =
      controlledMatrix (fun state => (branch.selectorBasis state).1 = label) (branch.placeMatrix u) := by
  classical
  ext row col
  change selectorCall label u (branch.selectorBasis row) (branch.selectorBasis col) = _
  by_cases active : (branch.selectorBasis row).1 = label ∧ (branch.selectorBasis col).1 = label
  · have same : (branch.selectorBasis row).1 = (branch.selectorBasis col).1 :=
      active.1.trans active.2.symm
    have spectators : ∀ i : {i : Fin n // i ∉ Set.range branch}, row i.val = col i.val :=
      fun bit => congrFun same bit
    simp only [selectorCall, controlledMatrix, ite_eq_left active, select, Matrix.of_apply,
      ite_eq_left same, branch.placeMatrix_apply, ite_eq_left spectators]
    rfl
  · simp only [selectorCall, controlledMatrix, ite_eq_right active, Matrix.one_apply,
      branch.selectorBasis.injective.eq_iff]

omit [Fintype J] [Fintype H] in
theorem select_one :
    select (fun _ : J => (1 : Matrix H H ℂ)) = 1 := by
  ext ⟨a, r⟩ ⟨b, c⟩
  by_cases same : a = b <;> simp [select, one_apply, same]

omit [DecidableEq H] in
theorem select_mul (u v : J → Matrix H H ℂ) :
    select u * select v = select (fun j => u j * v j) := by
  classical
  ext ⟨a, r⟩ ⟨b, c⟩
  by_cases same : a = b
  · subst b
    simp [mul_apply, Fintype.sum_prod_type, select, ite_mul, mul_ite]
  · simp [mul_apply, Fintype.sum_prod_type, select, ite_mul, mul_ite, same]

/-- Exactly one guarded call per label realizes block-diagonal SELECT. The order is arbitrary. -/
theorem selectorCalls_word (order : List J) (unique : order.Nodup)
    (branches : J → Matrix H H ℂ) :
    wordMatrix (order.map fun j => selectorCall j (branches j)) =
      select (fun j => if j ∈ order then branches j else 1) := by
  induction order with
  | nil => simpa [wordMatrix] using (select_one (J := J) (H := H)).symm
  | cons head tail ih =>
    rw [List.nodup_cons] at unique
    simp only [List.map_cons, wordMatrix]
    rw [ih unique.2, selectorCall_eq_select, select_mul]
    apply congrArg select
    funext j
    by_cases same : j = head
    · subst j
      simp [unique.1]
    · simp [same]

/-- A selector initialized to `zero` with the logical wires embedded by `frame`. -/
noncomputable def selectPrepareFrame (zero : J) (frame : Matrix H I ℂ) : Matrix (J × H) I ℂ :=
  prepareLift (Ket zero) * frame

omit [Fintype I] [DecidableEq I] in
/-- A selector may be the exact matrix of a serialized gate word. Its actual preparation
amplitudes determine the coefficients after unpreparing and projecting the signal wires. -/
theorem selectPrepare_compress (zero : J) (prepare : Matrix J J ℂ)
    (branches : J → Matrix H H ℂ) (frame : Matrix H I ℂ) :
    let lifted := prepareRegister (I := H) prepare
    let a := prepare *ᵥ Ket zero
    compress (selectPrepareFrame zero frame) (liftedᴴ * select branches * lifted)
      (selectPrepareFrame zero frame) =
      ∑ j, (star (a j) * a j) • compress frame (branches j) frame := by
  dsimp only
  let lifted := prepareRegister (I := H) prepare
  let initial : Matrix (J × H) H ℂ := prepareLift (Ket zero)
  let a := prepare *ᵥ Ket zero
  change compress (initial * frame) (liftedᴴ * select branches * lifted) (initial * frame) = _
  have prepareFrame : lifted * initial = prepareLift a :=
    prepareRegister_mul_prepareLift prepare (Ket zero)
  have factor :
      compress (initial * frame) (liftedᴴ * select branches * lifted) (initial * frame) =
        compress frame (compress (lifted * initial) (select branches) (lifted * initial)) frame := by
    simp only [compress, conjTranspose_mul, Matrix.mul_assoc]
  rw [factor, prepareFrame, prepare_select_compress]
  simp only [compress, lcuMatrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, a]

omit [DecidableEq J] in
/-- Quantitative substitution for a caller whose projected action is a
weighted sum of its slot blocks. Each slot supplies an error on its logical
block and the caller supplies the coefficient error. No bound on the
off-block part of a provider is needed. -/
theorem weighted_blocks_error (ideal actual : J → ℂ) (targets blocks : J → Matrix I I ℂ)
    (componentError coefficientError blockNorm : J → ℝ)
    (branch : ∀ j, ‖targets j - blocks j‖ ≤ componentError j)
    (weight : ∀ j, ‖ideal j - actual j‖ ≤ coefficientError j)
    (bound : ∀ j, ‖blocks j‖ ≤ blockNorm j) :
    ‖(∑ j, ideal j • targets j) - ∑ j, actual j • blocks j‖ ≤
      ∑ j, (‖ideal j‖ * componentError j + coefficientError j * blockNorm j) := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  calc
    _ = ‖ideal j • (targets j - blocks j) + (ideal j - actual j) • blocks j‖ := by
      rw [smul_sub, sub_smul, sub_add_sub_cancel]
    _ ≤ ‖ideal j • (targets j - blocks j)‖ + ‖(ideal j - actual j) • blocks j‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left (branch j) (norm_nonneg _))
        (mul_le_mul (weight j) (bound j) (norm_nonneg _) ((norm_nonneg _).trans (weight j)))

/-- A complete guarded word and actual preparation give a quantitative
block bound using only component, coefficient and component-norm contracts. -/
theorem selectPrepare_word_error (order : List J) (unique : order.Nodup)
    (complete : ∀ j : J, j ∈ order) (zero : J) (prepare : Matrix J J ℂ)
    (branches : J → Matrix H H ℂ) (frame : Matrix H I ℂ) (scale : ℂ)
    (ideal : J → ℂ) (targets : J → Matrix I I ℂ)
    (componentError coefficientError blockNorm : J → ℝ)
    (branch : ∀ j, ‖targets j - compress frame (branches j) frame‖ ≤ componentError j)
    (weight : ∀ j, ‖ideal j - scale * (star ((prepare *ᵥ Ket zero) j) *
      (prepare *ᵥ Ket zero) j)‖ ≤ coefficientError j)
    (bound : ∀ j, ‖compress frame (branches j) frame‖ ≤ blockNorm j) :
    let lifted := prepareRegister (I := H) prepare
    let initial := selectPrepareFrame zero frame
    let chosen := wordMatrix (order.map fun j => selectorCall j (branches j))
    ‖(∑ j, ideal j • targets j) -
      scale • compress initial (liftedᴴ * chosen * lifted) initial‖ ≤
        ∑ j, (‖ideal j‖ * componentError j + coefficientError j * blockNorm j) := by
  dsimp only
  rw [selectorCalls_word order unique, show
    (fun j => if j ∈ order then branches j else 1) = branches by
      funext j
      exact ite_eq_left (complete j), selectPrepare_compress, Finset.smul_sum]
  simp only [smul_smul]
  exact weighted_blocks_error _ _ _ _ _ _ _ branch weight bound

end OracqVerify.RIR
