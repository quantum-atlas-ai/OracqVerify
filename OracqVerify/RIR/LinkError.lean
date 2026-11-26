module

public import OracqVerify.RIR.ScopedLink
public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-! Operator-norm bounds for the semantic boundaries of a resolved call. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.ReferenceError.RefTraceError Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Matrix Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Compressing the difference between two actions to the same input and output
frames is nonexpansive. The two frames can describe clean scope exit or a
projection used for readout. Only the former licenses substituting the result as
an ordinary unitary call. -/
theorem compress_distance_le {L R : Matrix H I ℂ} (hL : IsIsometry L) (hR : IsIsometry R)
    (u v : Matrix H H ℂ) : ‖compress L u R - compress L v R‖ ≤ ‖u - v‖ := by
  have diff : compress L u R - compress L v R = compress L (u - v) R := by
    simp only [compress, Matrix.mul_sub, Matrix.sub_mul]
  have leftNorm : ‖Lᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_norm_le hL
  rw [diff]
  change ‖(Lᴴ * (u - v)) * R‖ ≤ ‖u - v‖
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (isometry_norm_le hR)).trans
      ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) leftNorm)))

/-- Coherent control cancels the common inactive identity. The difference is
sandwiched by the diagonal projection onto the active control sector. -/
theorem controlledMatrix_distance_le (active : I → Prop) (u v : Matrix I I ℂ) :
    ‖controlledMatrix active u - controlledMatrix active v‖ ≤ ‖u - v‖ := by
  classical
  let d : I → ℂ := fun i => if active i then 1 else 0
  let P := Matrix.diagonal d
  have normP : ‖P‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases h : active i <;> simp [d, h]
  have diff : controlledMatrix active u - controlledMatrix active v = P * (u - v) * P := by
    ext row col
    by_cases hRow : active row <;> by_cases hCol : active col <;>
      simp [controlledMatrix, P, d, Matrix.diagonal_mul, Matrix.mul_diagonal, hRow, hCol]
  rw [diff]
  exact l2_norm_sandwich_le _ _ _ normP normP

/-- Ordered wire placement preserves the operator-norm error. Spectator wires
are tensored with identity, then the full basis is relabeled. -/
theorem View.placeMatrix_distance {n k : Nat} (view : View n k) (u v : WireMatrix k) :
    ‖view.placeMatrix u - view.placeMatrix v‖ = ‖u - v‖ := by
  classical
  let A : Matrix (Spectators view) (Spectators view) ℂ := 1
  let : Nonempty (Spectators view) := ⟨fun _ => false⟩
  change ‖relabelGate view.splitBasis.symm (TensorGate u A) -
    relabelGate view.splitBasis.symm (TensorGate v A)‖ = _
  rw [l2_norm_relabelGate_sub]
  exact (l2_tensor_ancilla_error (J := Spectators view) u v).1

/-- Bounds are indexed by actual call sites. A surrounding adjoint or control
commutes with accounting for the same occurrence. -/
def ResolvedInstruction.callBudget (cost : CallSite → ℝ) : ResolvedInstruction → ℝ
  | .query name arguments banks => cost ⟨name, arguments, banks⟩
  | .adjoint body | .controlled _ body => body.callBudget cost
  | _ => 0

/-- Two already validated interpretations of the same instruction take the
same lexical arguments and differ only in the oracle environment. -/
theorem ResolvedInstruction.distance_le {n : Nat} (snapshot : Snapshot)
    (reference actual : Oracle n) (cost : CallSite → ℝ)
    (calls : ∀ site u v, reference site = .ok u → actual site = .ok v → ‖u - v‖ ≤ cost site)
    (step : ResolvedInstruction) {u v : WireMatrix n}
    (left : step.matrixWith n snapshot reference = .ok u)
    (right : step.matrixWith n snapshot actual = .ok v) :
    ‖u - v‖ ≤ step.callBudget cost := by
  induction step generalizing u v with
  | query name arguments banks => exact calls ⟨name, arguments, banks⟩ _ _ left right
  | adjoint body ih =>
    cases hu : body.matrixWith n snapshot reference <;>
      cases hv : body.matrixWith n snapshot actual <;>
      simp [ResolvedInstruction.matrixWith, hu, hv, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at left right
    subst u
    subst v
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    exact ih hu hv
  | controlled guard body ih =>
    cases placed : View.ofWires n guard.wires.length guard.wires <;>
      cases hu : body.matrixWith n snapshot reference <;>
      cases hv : body.matrixWith n snapshot actual <;>
      simp [ResolvedInstruction.matrixWith, placed, hu, hv, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at left right
    subst u
    subst v
    exact (controlledMatrix_distance_le _ _ _).trans (ih hu hv)
  | unary _ _ | xor _ _ | addConst _ _ | load _ _ _ | gphase _ =>
    have eq := Except.ok.inj (left.symm.trans right)
    simp [eq, ResolvedInstruction.callBudget]

private theorem word_distance {n : Nat} (s : Snapshot) (ref impl : Oracle n)
    (cost : CallSite → ℝ)
    (calls : ∀ site u v, ref site = .ok u → impl site = .ok v → ‖u - v‖ ≤ cost site)
    (steps : List ResolvedInstruction)
    (contracts : ∀ step ∈ steps, ∀ u v,
      step.matrixWith n s ref = .ok u → step.matrixWith n s impl = .ok v →
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1)
    {first second : List (WireMatrix n)}
    (left : steps.mapM (ResolvedInstruction.matrixWith n s ref) = .ok first)
    (right : steps.mapM (ResolvedInstruction.matrixWith n s impl) = .ok second) :
    ‖wordMatrix first‖ ≤ 1 ∧ ‖wordMatrix second‖ ≤ 1 ∧
      ‖wordMatrix first - wordMatrix second‖ ≤
        (steps.map (ResolvedInstruction.callBudget cost)).sum := by
  induction steps generalizing first second with
  | nil =>
    cases left
    cases right
    simp only [List.map_nil, List.sum_nil, sub_self, norm_zero, le_refl, and_true]
    exact ⟨l2_norm_one_le, l2_norm_one_le⟩
  | cons step rest ih =>
    cases hu : step.matrixWith n s ref <;>
      cases hv : step.matrixWith n s impl <;>
      cases hFirst : rest.mapM (ResolvedInstruction.matrixWith n s ref) <;>
      cases hSecond : rest.mapM (ResolvedInstruction.matrixWith n s impl) <;>
      simp [List.mapM_cons, hu, hv, hFirst, hSecond, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at left right
    subst first
    subst second
    have head := contracts step List.mem_cons_self _ _ hu hv
    have tail := ih
      (fun a mem => contracts a (List.mem_cons_of_mem step mem)) hFirst hSecond
    have stepError := step.distance_le s ref impl cost calls hu hv
    simp only [wordMatrix, List.map_cons, List.sum_cons]
    refine ⟨(norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) head.1).trans tail.1),
      (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) head.2).trans tail.2.1), ?_⟩
    refine (l2_norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [add_comm (step.callBudget cost)]
    exact (add_le_add (mul_le_of_le_one_right (norm_nonneg _) head.1)
      (mul_le_of_le_one_left (norm_nonneg _) tail.2.1)).trans (add_le_add tail.2.2 stepError)

/-- Operator-norm linking of a retained scoped body from local call contracts.
Both evaluations must have a clean, unitary exit. Each occurrence of a callee
adds its cost, with control and adjoint charged at the same cost. -/
theorem ScopedModule.distance_le (m : ScopedModule) (s : Snapshot)
    (ref impl : Oracle m.width) (cost : CallSite → ℝ)
    (calls : ∀ site u v, ref site = .ok u → impl site = .ok v → ‖u - v‖ ≤ cost site)
    (steps : List ResolvedInstruction) (body : m.body = some steps)
    (contracts : ∀ step ∈ steps, ∀ u v,
      step.matrixWith m.width s ref = .ok u → step.matrixWith m.width s impl = .ok v →
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1)
    {u v : WireMatrix m.width} (left : m.Certificate s ref u) (right : m.Certificate s impl v) :
    ‖m.publicMatrix u - m.publicMatrix v‖ ≤
      (steps.map (ResolvedInstruction.callBudget cost)).sum := by
  have hu := left.body
  have hv := right.body
  cases eu : steps.mapM (ResolvedInstruction.matrixWith m.width s ref) <;>
    cases ev : steps.mapM (ResolvedInstruction.matrixWith m.width s impl) <;>
    simp [ScopedModule.bodyMatrix, body, eu, ev, Bind.bind, Except.bind, Pure.pure, Except.pure]
      at hu hv
  subst u
  subst v
  exact (compress_distance_le m.frame_isIsometry m.frame_isIsometry _ _).trans
    (word_distance s ref impl cost calls steps contracts eu ev).2.2

/-- An error contract stated on a callee's public interface is transported to
a resolved call with the same ordered view and the same forwarded snapshot. -/
theorem ScopedEnvironment.atCall_distance {n k : Nat} (ref impl : ScopedEnvironment)
    (site : CallSite) (snapshot : Snapshot) (banks : List Resource)
    (reference actual : Snapshot → Except String (WireMatrix k))
    (refFound : lookup ref site.name "scoped callee" = .ok ⟨k, banks, reference⟩)
    (implFound : lookup impl site.name "scoped callee" = .ok ⟨k, banks, actual⟩)
    (child : Snapshot) (forwarded : snapshot.forward banks site.banks = .ok child)
    (cost : ℝ) (contract : ∀ a b, reference child = .ok a → actual child = .ok b → ‖a - b‖ ≤ cost)
    {u v : WireMatrix n}
    (left : ref.atCall n snapshot site = .ok u) (right : impl.atCall n snapshot site = .ok v) :
    ‖u - v‖ ≤ cost := by
  cases view : View.ofWires n k site.arguments.flatten <;>
    cases eu : reference child <;> cases ev : actual child <;>
    simp [ScopedEnvironment.atCall, refFound, implFound, view, forwarded, eu, ev,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at left right
  subst u
  subst v
  rw [View.placeMatrix_distance]
  exact contract _ _ eu ev

end OracqVerify.RIR
