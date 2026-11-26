module

public import OracqVerify.RIR.ScopedSubgraph
public import OracqVerify.RIR.GateAction

/-! The product of an ordered list of independent one-wire gates. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

noncomputable def wireTensor {n : Nat} (gates : Fin n → Matrix Bool Bool ℂ) : WireMatrix n :=
  Matrix.of fun row col => ∏ i, gates i (row i) (col i)

theorem wireTensor_one (n : Nat) : wireTensor (fun _ : Fin n => 1) = 1 := by
  classical
  ext row col
  by_cases eq : row = col
  · subst col
    simp [wireTensor, Matrix.one_apply]
  · obtain ⟨wire, different⟩ : ∃ i, row i ≠ col i := by
      by_contra! all
      exact eq (funext all)
    simp only [wireTensor, Matrix.of_apply]
    rw [Finset.prod_eq_zero (Finset.mem_univ wire) (by simp [different])]
    simp [eq]

theorem wireTensor_mul {n : Nat} (u v : Fin n → Matrix Bool Bool ℂ) :
    wireTensor u * wireTensor v = wireTensor (fun i => u i * v i) := by
  classical
  ext row col
  simp only [wireTensor, Matrix.of_apply, Matrix.mul_apply, ← Finset.prod_mul_distrib,
    Fintype.prod_sum]

theorem wireTensor_single {n : Nat} (wire : Fin n) (g : Matrix Bool Bool ℂ) :
    wireTensor (fun i => if i = wire then g else 1) = atWire wire g := by
  classical
  ext row col
  change (∏ i, (if i = wire then g else 1) (row i) (col i)) =
    (if ∀ i : Fin n, i ≠ wire → row i = col i then g (row wire) (col wire) else 0)
  by_cases same : ∀ i : Fin n, i ≠ wire → row i = col i
  · rw [ite_eq_left same]
    rw [Finset.prod_eq_single wire]
    · simp
    · intro i _ ne
      simp [ne, Matrix.one_apply, same i ne]
    · simp
  · rw [ite_eq_right same]
    push Not at same
    obtain ⟨i, ne, changed⟩ := same
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [ne, changed])

theorem wordMatrix_atWires {n : Nat} (wires : List (Fin n)) (distinct : wires.Nodup)
    (g : Fin n → Matrix Bool Bool ℂ) :
    wordMatrix (wires.map fun i => atWire i (g i)) =
      wireTensor (fun i => if i ∈ wires then g i else 1) := by
  induction wires with
  | nil => simpa only [List.map_nil, wordMatrix, List.not_mem_nil, ite_false] using (wireTensor_one n).symm
  | cons a tail ih =>
    rw [List.nodup_cons] at distinct
    rw [List.map_cons, wordMatrix, ih distinct.2, ← wireTensor_single, wireTensor_mul]
    congr 1
    funext i
    by_cases h : i = a
    · subst i
      simp [distinct.1]
    · simp only [h, ite_false, mul_one, List.mem_cons, false_or]

theorem allHadamards (n : Nat) (memory : Snapshot) (oracle : Oracle n) :
    (ResolvedInstruction.unary .h (List.range n)).matrixWith n memory oracle = .ok (HadamardN n) := by
  unfold ResolvedInstruction.matrixWith ResolvedInstruction.matrix
  rw [List.length_range]
  simp only [View.ofWires_range, Bind.bind, Except.bind, Pure.pure, Except.pure]
  change Except.ok (wordMatrix ((List.finRange n).map fun i => atWire i Hadamard)) = _
  rw [wordMatrix_atWires _ (List.nodup_finRange n), show
    (fun i : Fin n => if i ∈ List.finRange n then Hadamard else 1) = fun _ => Hadamard by
    funext i; simp]
  rfl

end OracqVerify.RIR
