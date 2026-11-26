module

public import OracqVerify.Verification.LCHSLink
public import OracqVerify.RIR.Fanout
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-! A wider LCHS family obtained by entangling the target basis around a linked
assembly. The verifier checks the added wires and gates symbolically. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.WideLCHS

open OracqVerify.RIR OracqVerify.Verification.LCHS
open Matrix Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.Execution.WorkspaceCP Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open scoped Matrix Matrix.Norms.L2Operator Kronecker

def firstWire (d : Nat) : Fin (10+d) := Fin.castAdd d 0

def innerView (d : Nat) : View (10+d) 10 :=
  ⟨Fin.castAdd d, fun _ _ h => Fin.ext (congrArg (Fin.val : Fin (10+d) → Nat) h)⟩

def extraWire {d : Nat} (i : Fin d) : Fin (10+d) := Fin.natAdd 10 i

private theorem wireApart {d : Nat} (i : Fin d) : firstWire d ≠ extraWire i := by
  intro same
  have h : 0 = 10 + i.val := congrArg Fin.val same
  omega

def cnot {d : Nat} (i : Fin d) : GateAction (10+d) :=
  let guard : View (10+d) 1 := ⟨fun _ => firstWire d, fun a b _ => Subsingleton.elim a b⟩
  .control guard 1 (.unary .x (extraWire i) false)

def fanout (d : Nat) : List (GateAction (10+d)) := (List.finRange d).map cnot

def toggle {d : Nat} (wires : Finset (Fin d)) (state : Reg (10+d)) : Reg (10+d) :=
  Fin.addCases (fun i => state (Fin.castAdd d i))
    (fun i => if i ∈ wires ∧ state (firstWire d) = true then !state (extraWire i)
      else state (extraWire i))

@[simp] private theorem toggle_core {d : Nat} (wires : Finset (Fin d)) (s : Reg (10+d)) (i : Fin 10) :
    toggle wires s (Fin.castAdd d i) = s (Fin.castAdd d i) := by simp [toggle]

@[simp] private theorem toggle_extra {d : Nat} (wires : Finset (Fin d)) (s : Reg (10+d)) (i : Fin d) :
    toggle wires s (extraWire i) =
      if i ∈ wires ∧ s (firstWire d) = true then !s (extraWire i) else s (extraWire i) := by
  simp [toggle, extraWire]

private theorem toggle_empty {d : Nat} : toggle (∅ : Finset (Fin d)) = id := by
  funext state wire
  refine Fin.addCases (fun i => by simp) (fun i => ?_) wire
  change toggle ∅ state (extraWire i) = state (extraWire i)
  simp

private theorem toggle_cons {d : Nat} (i : Fin d) (wires : Finset (Fin d))
    (fresh : i ∉ wires) :
    toggle wires ∘ cnotBasis (firstWire d) (extraWire i) = toggle (insert i wires) := by
  funext s wire
  change toggle wires (cnotBasis (firstWire d) (extraWire i) s) wire = _
  refine Fin.addCases (fun j => ?_) (fun j => ?_) wire
  · simp only [toggle_core]
    have apart : Fin.castAdd d j ≠ extraWire i := by
      intro same
      have h : j.val = 10 + i.val := congrArg Fin.val same
      omega
    unfold cnotBasis
    split
    · exact Function.update_of_ne apart _ _
    · rfl
  · change toggle wires (cnotBasis (firstWire d) (extraWire i) s) (extraWire j) =
      toggle (insert i wires) s (extraWire j)
    simp only [toggle_extra, cnotBasis_preserves (wireApart i)]
    by_cases control : s (firstWire d) = true
    · by_cases hit : j = i
      · subst j
        simp [cnotBasis, control, flipAt, fresh]
      · have notEqual : extraWire j ≠ extraWire i := by
          intro e
          apply hit
          apply Fin.ext
          have same : 10 + j.val = 10 + i.val := congrArg (Fin.val : Fin (10+d) → Nat) e
          omega
        simp [cnotBasis, control, flipAt, Function.update_of_ne notEqual, Finset.mem_insert, hit]
    · simp [cnotBasis, control]

private theorem cnot_word {d : Nat} (wires : List (Fin d)) (distinct : wires.Nodup) :
    wordMatrix ((wires.map cnot).map GateAction.matrix) = permMatrix (toggle wires.toFinset) := by
  induction wires with
  | nil =>
    rw [List.toFinset_nil, toggle_empty]
    ext r c
    simp [wordMatrix, permMatrix, Matrix.one_apply]
  | cons i rest ih =>
    rw [List.nodup_cons] at distinct
    rw [List.map_cons, List.map_cons, wordMatrix, ih distinct.2,
      cnot, controlledX_matrix _ _ (wireApart i), permMatrix_comp, toggle_cons,
      List.toFinset_cons]
    exact fun h => distinct.1 (List.mem_toFinset.mp h)

theorem toggle_involutive (d : Nat) : Function.Involutive
    (toggle (Finset.univ : Finset (Fin d))) := by
  intro state
  funext wire
  refine Fin.addCases (fun i => ?_) (fun i => ?_) wire
  · simp
  · change toggle Finset.univ (toggle Finset.univ state) (extraWire i) = state (extraWire i)
    simp only [toggle_extra, firstWire, toggle_core, Finset.mem_univ, true_and]
    by_cases active : state (Fin.castAdd d 0) = true <;> simp [active]

def physicalFanout (d : Nat) : Reg (10+d) ≃ Reg (10+d) :=
  (toggle_involutive d).toPerm _

theorem fanout_matrix (d : Nat) :
    wordMatrix ((fanout d).map GateAction.matrix) = permMatrix (physicalFanout d) := by
  rw [fanout, cnot_word _ (List.nodup_finRange d), show (List.finRange d).toFinset = Finset.univ by
    ext i; simp]
  rfl

/-- Logical coordinates separate the original data bit from the added data register. -/
abbrev Data (d : Nat) := Bool × Reg d

def toggleData {d : Nat} (x : Data d) : Data d :=
  (x.1, if x.1 then fun i => !x.2 i else x.2)

theorem toggleData_involutive (d : Nat) : Function.Involutive (@toggleData d) := by
  rintro ⟨b, extra⟩
  cases b <;> simp [toggleData]

def logicalFanout (d : Nat) : Data d ≃ Data d :=
  (toggleData_involutive d).toPerm _

noncomputable def outputView (d : Nat) : Data d ↪ Reg (10+d) where
  toFun x := Fin.addCases (outputFrame x.1) x.2
  inj' := by
    intro a b h
    apply Prod.ext
    · apply outputFrame.injective
      funext i
      simpa using congrFun h (Fin.castAdd d i)
    · funext i
      simpa [extraWire] using congrFun h (extraWire i)

@[simp] private theorem outputView_core (d : Nat) (x : Data d) (i : Fin 10) :
    outputView d x (Fin.castAdd d i) = outputFrame x.1 i := by
  simp [outputView]

@[simp] private theorem outputView_extra (d : Nat) (x : Data d) (i : Fin d) :
    outputView d x (extraWire i) = x.2 i := by
  simp [outputView, extraWire]

private theorem outputView_control (d : Nat) (x : Data d) :
    outputView d x (firstWire d) = x.1 := by
  rw [firstWire, outputView_core, outputFrame_order]
  simp [GateEvidence.zeroSignal]

private theorem fanout_outputView (d : Nat) (x : Data d) :
    physicalFanout d (outputView d x) = outputView d (logicalFanout d x) := by
  funext wire
  change toggle Finset.univ (outputView d x) wire = outputView d (toggleData x) wire
  refine Fin.addCases (fun i => ?_) (fun i => ?_) wire
  · simp [toggleData]
  · change toggle Finset.univ (outputView d x) (extraWire i) = outputView d (toggleData x) (extraWire i)
    simp only [toggle_extra, outputView_control, Finset.mem_univ, true_and, outputView_extra]
    by_cases control : x.1 = true <;> simp [toggleData, control]

noncomputable def liftBlock (d : Nat) (a : Matrix Bool Bool ℂ) : Matrix (Data d) (Data d) ℂ :=
  relabelGate (logicalFanout d) (TensorGate a (1 : WireMatrix d))

theorem liftBlock_distance (d : Nat) (a b : Matrix Bool Bool ℂ) :
    ‖liftBlock d a - liftBlock d b‖ = ‖a - b‖ := by
  unfold liftBlock
  rw [l2_norm_relabelGate_sub]
  exact (l2_tensor_ancilla_error (J := Reg d) a b).1

theorem liftBlock_smul (d : Nat) (r : ℝ) (a : Matrix Bool Bool ℂ) :
    liftBlock d (r • a) = r • liftBlock d a := by
  ext row col
  simp [liftBlock, relabelGate, TensorGate, Matrix.smul_apply, mul_assoc]

/-- The lifted Hamiltonian is an algebraic change of representation. -/
noncomputable def liftAlgebra (d : Nat) :
    Matrix Bool Bool ℂ →ₐ[ℂ] Matrix (Data d) (Data d) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (logicalFanout d)).toAlgHom.comp
    { toFun := fun a => TensorGate a (1 : WireMatrix d)
      map_one' := tensorGate_one
      map_zero' := Matrix.zero_kronecker _
      map_add' := fun a b => Matrix.add_kronecker a b _
      map_mul' := fun a b => by
        rw [tensorGate_mul, Matrix.one_mul]
      commutes' := fun r => by
        simp only [Algebra.algebraMap_eq_smul_one, TensorGate, Matrix.smul_kronecker,
          Matrix.one_kronecker_one] }

theorem liftAlgebra_apply (d : Nat) (a : Matrix Bool Bool ℂ) :
    liftAlgebra d a = liftBlock d a := rfl

theorem liftBlock_evolution (d : Nat) (a : Matrix Bool Bool ℂ) (t : ℝ) :
    liftBlock d (hamiltonianEvolution a t) = hamiltonianEvolution (liftBlock d a) t := by
  let : NormedAlgebra ℚ (Matrix Bool Bool ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Matrix (Data d) (Data d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  change liftAlgebra d (NormedSpace.exp _) = NormedSpace.exp (_ • liftAlgebra d a)
  rw [NormedSpace.map_exp (liftAlgebra d) (liftAlgebra d).toLinearMap.continuous_of_finiteDimensional,
    map_smul]

theorem liftBlock_quadrature (d : Nat) (l h : Matrix Bool Bool ℂ) (t : ℝ) (cutoff nodes : Nat) :
    liftBlock d (staticLchsQuadrature l h t cutoff nodes) =
      staticLchsQuadrature (liftBlock d l) (liftBlock d h) t cutoff nodes := by
  unfold staticLchsQuadrature
  rw [← liftAlgebra_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, liftAlgebra_apply, liftBlock_evolution]
  congr 2
  rw [← liftAlgebra_apply, map_add, liftAlgebra_apply, liftAlgebra_apply, liftBlock_smul]

/-- The signal projection commutes with the extra target wires, and the
outer conjugation restricts to the fanout on the full logical register. -/
theorem compress_wide (d : Nat) (u : WireMatrix 10) :
    compress (basisFrame (outputView d))
      (permMatrix (physicalFanout d).symm * (innerView d).placeMatrix u * permMatrix (physicalFanout d))
      (basisFrame (outputView d)) =
      liftBlock d (compress (basisFrame outputFrame) u (basisFrame outputFrame)) := by
  classical
  ext row col
  rw [basisFrame_compress, permMatrix_sandwich, fanout_outputView, fanout_outputView,
    View.placeMatrix_apply]
  let r := logicalFanout d row
  let c := logicalFanout d col
  have equal : (∀ i : {i : Fin (10+d) // i ∉ Set.range (innerView d)},
      outputView d r i.val = outputView d c i.val) ↔ r.2 = c.2 := by
    constructor
    · intro spectators
      funext i
      have outside : extraWire i ∉ Set.range (innerView d) := by
        intro ⟨j, eq⟩
        have same : j.val = 10 + i.val := congrArg Fin.val eq
        omega
      simpa using spectators ⟨extraWire i, outside⟩
    · intro equal ⟨i, outside⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i outside
      · intro missing
        exact (missing ⟨j, rfl⟩).elim
      · intro _
        change outputView d r (extraWire ‹Fin d›) = outputView d c (extraWire ‹Fin d›)
        simp [equal]
  have core (x : Data d) : outputView d x ∘ innerView d = outputFrame x.1 := by
    funext i
    exact outputView_core d x i
  simp only [core]
  have replace : (if ∀ i : {i : Fin (10+d) // i ∉ Set.range (innerView d)},
        outputView d r i.val = outputView d c i.val then u (outputFrame r.1) (outputFrame c.1) else 0) =
      (if r.2 = c.2 then u (outputFrame r.1) (outputFrame c.1) else 0) := by
    by_cases same : r.2 = c.2
    · rw [ite_eq_left (equal.mpr same), ite_eq_left same]
    · rw [ite_eq_right (fun inside => same (equal.mp inside)), ite_eq_right same]
  rw [replace]
  have selfInverse (x : Data d) : (logicalFanout d).symm x = logicalFanout d x := rfl
  change (if r.2 = c.2 then u (outputFrame r.1) (outputFrame c.1) else 0) = _
  unfold liftBlock
  change _ = TensorGate _ (1 : WireMatrix d) ((logicalFanout d).symm row) ((logicalFanout d).symm col)
  simp [selfInverse, r, c, TensorGate, Matrix.one_apply, basisFrame_compress, mul_ite]

/-- Assemble the expected wide trace from the independently certified inner
word. The conditions here have no numerical state-vector size limits. -/
def expectedWord (d : Nat) (inner : List (GateAction 10)) : List (GateAction (10+d)) :=
  fanout d ++ inner.map (GateAction.place (innerView d)) ++
    (fanout d).reverse.map GateAction.inverse

noncomputable def matrixWide (d : Nat) (inner : List (GateAction 10)) : WireMatrix (10+d) :=
  wordMatrix ((expectedWord d inner).map GateAction.matrix)

theorem matrixWide_eq (d : Nat) (inner : List (GateAction 10)) :
    matrixWide d inner = permMatrix (physicalFanout d).symm *
      (innerView d).placeMatrix (wordMatrix (inner.map GateAction.matrix)) *
      permMatrix (physicalFanout d) := by
  have reverse :
      (((fanout d).reverse.map GateAction.inverse).map GateAction.matrix) =
        (((fanout d).map GateAction.matrix).reverse.map Matrix.conjTranspose) := by
    simp only [List.map_map, ← List.map_reverse, Function.comp_def, GateAction.inverse_matrix]
  have starPerm : (permMatrix (physicalFanout d))ᴴ = permMatrix (physicalFanout d).symm := by
    ext row col
    simp [permMatrix, conjTranspose_apply, eq_comm, Equiv.eq_symm_apply]
  unfold matrixWide expectedWord
  rw [List.map_append, List.map_append, wordMatrix_append, wordMatrix_append,
    reverse, wordMatrix_reverse_adjoint, fanout_matrix, starPerm, GateAction.placed_word, mul_assoc]

open Lean

def coreName (program : Program) : Except String String := do
  let root ← lookupModule program program.entry
  let some body := root.body | throw "Expected a concrete wide LCHS caller"
  let [name] := body.filterMap (fun
    | .call name _ _ => some name
    | _ => none)
    | throw "The wide LCHS caller must call one linked assembly"
  return name

structure Caller (source : Program) where
  name : String
  core : OpenAssembly (reroot source name)
  scale : readScale source = .ok core.scale

def certifyCaller (source : Program) : Except String (Caller source) := do
  let name ← coreName source
  let core ← certifyOpenAssembly (reroot source name)
  if scale : readScale source = .ok core.scale then
    return ⟨name, core, scale⟩
  else throw "Wide LCHS caller declares a different output normalization"

structure Certificate {source : Program} (caller : Caller source) (bound : Program) (d : Nat) where
  link : ScopedSourceLink source bound []
  core : LinkedAssembly caller.core (reroot bound caller.name)
  scale : readScale bound = .ok caller.core.scale
  trace : ResolvedProgram
  resolved : bound.resolve = .ok trace
  width : trace.wireCount = 10+d
  unitaryGates : trace.instructions.all (ResolvedInstruction.isUnitaryGate trace.wireCount) = true
  lowered : trace.instructions.mapM (GateAction.lower trace.wireCount false) =
    .ok (width.symm ▸ expectedWord d (actionsAt core.output core.outputWidth))

def certify {source : Program} (caller : Caller source) (bound : Program) (d : Nat) :
    Except String (Certificate caller bound d) := do
  let link ← verifyScopedSourceLink source bound
  let scale : Subtype (fun _ : Unit => readScale bound = .ok caller.core.scale) ←
    if h : readScale bound = .ok caller.core.scale then pure ⟨(), h⟩
    else throw "Wide LCHS bound program declares a different output normalization"
  let core ← certifyLinkedAssembly caller.core (reroot bound caller.name)
  match resolved : bound.resolve with
  | .error reason => throw reason
  | .ok resolvedTrace =>
    if width : resolvedTrace.wireCount = 10+d then
      if unitaryGates : resolvedTrace.instructions.all (ResolvedInstruction.isUnitaryGate resolvedTrace.wireCount) = true then
        if lowered : resolvedTrace.instructions.mapM (GateAction.lower resolvedTrace.wireCount false) =
            .ok (width.symm ▸ expectedWord d (actionsAt core.output core.outputWidth)) then
          return ⟨link, core, scale.2, resolvedTrace, resolved, width, unitaryGates, lowered⟩
        else throw "Wide LCHS gates differ from the prescribed fanout, assembly, and inverse"
      else throw "Wide LCHS contains a nonunitary gate or writes a control wire"
    else throw "Wide LCHS has an unexpected total width"

theorem Certificate.matrix {source bound : Program} {caller : Caller source} {d : Nat}
    (cert : Certificate caller bound d) :
    bound.matrix (fun _ => none) =
      .ok ⟨10+d, matrixWide d (actionsAt cert.core.output cert.core.outputWidth)⟩ ∧
      matrixWide d (actionsAt cert.core.output cert.core.outputWidth) ∈ Matrix.unitaryGroup (Reg (10+d)) ℂ := by
  let word := expectedWord d (actionsAt cert.core.output cert.core.outputWidth)
  have semantic := GateAction.resolved_matrix (fun _ => none) cert.lowered
  have each := GateAction.lower_unitary cert.unitaryGates cert.lowered
  have resulting : ∀ n (e : n = 10+d),
      (⟨n, wordMatrix ((e.symm ▸ word : List (GateAction n)).map GateAction.matrix)⟩ :
        Σ w, WireMatrix w) = ⟨10+d, matrixWide d (actionsAt cert.core.output cert.core.outputWidth)⟩ := by
    intro n equal
    subst n
    rfl
  constructor
  · simp only [Program.matrix, cert.resolved, semantic, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact congrArg Except.ok (resulting cert.trace.wireCount cert.width)
  · have all : wordMatrix ((cert.width.symm ▸ word : List (GateAction cert.trace.wireCount)).map
        GateAction.matrix) ∈ Matrix.unitaryGroup (Reg cert.trace.wireCount) ℂ := by
      apply wordMatrix_unitary
      simpa only [List.mem_map] using fun gate ⟨action, mem, same⟩ => same ▸ each action mem
    have transport (n : Nat) (e : n = 10+d)
        (h : wordMatrix ((e.symm ▸ word : List (GateAction n)).map GateAction.matrix) ∈
          Matrix.unitaryGroup (Reg n) ℂ) :
        matrixWide d (actionsAt cert.core.output cert.core.outputWidth) ∈
          Matrix.unitaryGroup (Reg (10+d)) ℂ := by
      subst n
      exact h
    exact transport _ cert.width all

/-- A wide accepted binding has the same quantitative error for the
fanout-conjugated quadrature, all without evaluating an ambient column. -/
theorem Certificate.sound {source bound : Program} {caller : Caller source} {d : Nat}
    (cert : Certificate caller bound d) :
    ∃ u : WireMatrix (10+d), bound.matrix (fun _ => none) = .ok ⟨10+d, u⟩ ∧
      BlockEncoding (staticLchsQuadrature (liftBlock d sampleL) (liftBlock d sampleH) (1 / 8) 1 4) u
        (basisFrame (outputView d)) (basisFrame (outputView d)) (caller.core.scale : ℝ) (1 / 50) := by
  let inner := actionsAt cert.core.output cert.core.outputWidth
  obtain ⟨evaluated, unitary⟩ := cert.matrix
  obtain ⟨_, _, base⟩ := cert.core.sound
  refine ⟨matrixWide d inner, evaluated, unitary, basisFrame_isIsometry _, basisFrame_isIsometry _,
    base.normalization_pos, base.error_nonneg, ?_⟩
  rw [matrixWide_eq, compress_wide, ← liftBlock_quadrature, ← liftBlock_smul, liftBlock_distance]
  exact base.error_le

end OracqVerify.Verification.WideLCHS
