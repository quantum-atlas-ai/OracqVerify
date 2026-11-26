module

public import OracqVerify.Verification.LCHSComponents
public import OracqVerify.RIR.ScopedSourceLink
public import OracqVerify.RIR.SelectPrepareWord

/-! Late binding of the four Hamiltonian simulation branches of a single LCHS caller. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.LCHS

open Lean RIR Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.CoherentSim.FactorialTaylor Qatlib.Concepts.QspSimulation.Achievability
open scoped Matrix Matrix.Norms.L2Operator

/-- Each provider adapts its own normalization and signal layout to the public interface. -/
def branchPorts : List Register := [⟨"target", ⟨.bits, 1⟩⟩, ⟨"signal", ⟨.bits, 7⟩⟩]

def checkSlot (source : Program) (name : String) : Except String Unit := do
  let slot ← lookupModule source name
  unless slot.body.isNone && slot.registers == branchPorts &&
      slot.resources.isEmpty && slot.locals.isEmpty do
    throw s!"Expected an open LCHS branch with the common interface at {name}"
  unless (← numericAttribute slot "be_alpha") == 2 do
    throw s!"Expected branch normalization two at {name}"

structure OpenAssembly (original : Program) where
  graph : ScopedProgram
  resolved : original.resolveScoped = .ok graph
  scale : ℚ
  scaleDecoded : readScale original = .ok scale
  positiveScale : 0 < scale
  smallScale : scale ≤ 1
  slots : Vector String 4
  prepare : String
  wiring : assembly original scale = .ok (slots, prepare)
  slotsMatch : scopedSlots graph = slots.toList
  interfaces : slots.toList.mapM (checkSlot original) = .ok [(), (), (), ()]
  selector : GateEvidence.Certificate (reroot original prepare)
  selectorWidth : selector.trace.wireCount = 2
  weights : ∀ j : Fin 4, |rationalPiLower * scale *
    GateEvidence.normSquare (selectorEntry selector j) - weightNumerator j * 2| ≤ 1 / 10^12

def certifyOpenAssembly (original : Program) : Except String (OpenAssembly original) := do
  match resolved : original.resolveScoped, scaleDecoded : readScale original with
  | .ok graph, .ok scale =>
    match wiring : assembly original scale with
    | .error reason => throw reason
    | .ok (slots, prepare) =>
      unless slots.toList.Nodup do throw "Expected four distinct LCHS slots"
      let isValid : Subtype (fun _ : Unit => 0 < scale ∧ scale ≤ 1) ←
        if h : 0 < scale ∧ scale ≤ 1 then pure ⟨(), h⟩
        else throw "Expected a positive LCHS normalization at most one"
      if slotsMatch : scopedSlots graph = slots.toList then
        match interfaces : slots.toList.mapM (checkSlot original) with
        | .error reason => throw reason
        | .ok [(), (), (), ()] =>
          let selector ← GateEvidence.certify (reroot original prepare)
          if selectorWidth : selector.trace.wireCount = 2 then
            if weights : ∀ j : Fin 4, |rationalPiLower * scale *
                GateEvidence.normSquare (selectorEntry selector j) - weightNumerator j * 2| ≤ 1 / 10^12 then
              return ⟨graph, resolved, scale, scaleDecoded, isValid.2.1, isValid.2.2, slots, prepare, wiring, slotsMatch,
                interfaces, selector, selectorWidth, weights⟩
            else throw "Open LCHS selector probabilities disagree with the common branch normalizations"
          else throw "Expected a two-wire selector in the open LCHS caller"
        | .ok _ => throw "Expected four open LCHS interfaces"
      else throw "Open LCHS program must expose the four branches in quadrature order"
  | .error reason, _ | _, .error reason => throw reason

def selectorWire : Fin 2 → Fin 10 := ![1, 2]
def branchWire : Fin 8 → Fin 10 := ![0, 3, 4, 5, 6, 7, 8, 9]

def layout : SelectLayout 10 2 8 where
  selector := ⟨selectorWire, by
    change ∀ i j, selectorWire i = selectorWire j → i = j
    decide⟩
  branch := ⟨branchWire, by
    change ∀ i j, branchWire i = branchWire j → i = j
    decide⟩
  apart := by
    change ∀ i j, selectorWire i ≠ branchWire j
    decide
  covers := by
    change ∀ i, (∃ j, selectorWire j = i) ∨ (∃ j, branchWire j = i)
    decide

def actionsAt {program : Program} (cert : GateEvidence.Certificate program) {n : Nat}
    (width : cert.trace.wireCount = n) : List (GateAction n) :=
  width ▸ cert.actions

noncomputable def matrixAt {program : Program} (cert : GateEvidence.Certificate program)
    {n : Nat} (width : cert.trace.wireCount = n) : WireMatrix n :=
  wordMatrix ((actionsAt cert width).map GateAction.matrix)

private theorem matrixAt_sound {program : Program} (cert : GateEvidence.Certificate program)
    {n : Nat} (width : cert.trace.wireCount = n) :
    program.matrix (fun _ => none) = .ok ⟨n, matrixAt cert width⟩ ∧
      matrixAt cert width ∈ unitaryGroup (Reg n) ℂ := by
  subst n
  exact cert.sound

def zeroFrame (n : Nat) (positive : 0 < n) : Bool ↪ Reg n where
  toFun := GateEvidence.zeroSignal n
  inj' := fun _ _ same => congrFun same ⟨0, positive⟩

def branchFrame : Bool ↪ Reg 8 := zeroFrame 8 (by decide)

noncomputable def outputFrame : Bool ↪ Reg 10 :=
  (branchFrame.trans (SelectLayout.tagged (fun _ => false : Reg 2))).trans layout.basis.symm.toEmbedding

theorem outputFrame_order (bit : Bool) :
    outputFrame bit = GateEvidence.zeroSignal 10 bit := by
  apply layout.basis.injective
  have tagged : layout.basis (outputFrame bit) = ((fun _ => false : Reg 2), branchFrame bit) :=
    layout.basis.apply_symm_apply ((fun _ => false : Reg 2), branchFrame bit)
  rw [tagged]
  change (fun _ => false, branchFrame bit) =
    (GateEvidence.zeroSignal 10 bit ∘ layout.selector, GateEvidence.zeroSignal 10 bit ∘ layout.branch)
  cases bit <;> decide +kernel

private theorem matrixAt_entry {program : Program} (cert : GateEvidence.Certificate program)
    {n : Nat} (width : cert.trace.wireCount = n) (r c : Reg n) :
    matrixAt cert width r c = cert.matrix (cast (congrArg Reg width.symm) r)
      (cast (congrArg Reg width.symm) c) := by
  subst n
  rfl

private theorem cast_zeroSignal {n m : Nat} (e : n = m) (bit : Bool) :
    cast (congrArg Reg e.symm) (GateEvidence.zeroSignal m bit) = GateEvidence.zeroSignal n bit := by
  subst m
  rfl

private theorem branchAt_block {program : Program} {j : Fin 4} (branch : Branch program j)
    (width : branch.evidence.trace.wireCount = 8) :
    branch.block = (branch.scale : ℝ) • compress (basisFrame branchFrame)
      (matrixAt branch.evidence width) (basisFrame branchFrame) := by
  ext r c
  simp only [Branch.block, Matrix.smul_apply, basisFrame_compress, matrixAt_entry]
  change (branch.scale : ℝ) • branch.evidence.matrix
      (GateEvidence.zeroSignal _ r) (GateEvidence.zeroSignal _ c) =
    (branch.scale : ℝ) • branch.evidence.matrix
      (cast (congrArg Reg width.symm) (GateEvidence.zeroSignal 8 r))
      (cast (congrArg Reg width.symm) (GateEvidence.zeroSignal 8 c))
  rw [cast_zeroSignal width r, cast_zeroSignal width c]

private theorem cast_label {n m : Nat} (e : n = m) (j : Nat) :
    cast (congrArg Reg e.symm) (SelectLayout.label (s := m) j) =
      SelectLayout.label (s := n) j := by
  subst m
  rfl

private theorem cast_false {n m : Nat} (e : n = m) :
    cast (congrArg Reg e.symm) (fun _ => false : Reg m) = (fun _ => false : Reg n) := by
  subst m
  rfl

private theorem selectorAt_entry {program : Program} (selector : GateEvidence.Certificate program)
    (width : selector.trace.wireCount = 2) (j : Fin 4) :
    matrixAt selector width (SelectLayout.label j.val) (fun _ => false) =
      selector.matrix (fun wire => Nat.testBit j.val wire.val) (fun _ => false) := by
  rw [matrixAt_entry, cast_label width, cast_false width]
  rfl

private theorem label_index (j : Fin 4) :
    SelectLayout.label (s := 2) j.val = (orderedBitsIndex 2).symm j := by
  fin_cases j <;> decide

private theorem labels_complete (label : Reg 2) :
    label ∈ (List.range 4).map (SelectLayout.label (s := 2)) := by
  let j : Fin 4 := orderedBitsIndex 2 label
  refine List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
  exact (label_index j).trans ((orderedBitsIndex 2).symm_apply_apply label)

def branchWords {bound : Program} {slots : Vector String 4}
    (branch : (j : Fin 4) → Branch (reroot bound slots[j]) j)
    (width : ∀ j, (branch j).evidence.trace.wireCount = 8) (label : Reg 2) : List (GateAction 8) :=
  let j := orderedBitsIndex 2 label
  actionsAt (branch j).evidence (width j)

private theorem branchWords_label {bound : Program} {slots : Vector String 4}
    (branch : (j : Fin 4) → Branch (reroot bound slots[j]) j)
    (width : ∀ j, (branch j).evidence.trace.wireCount = 8) (j : Fin 4) :
    branchWords branch width (SelectLayout.label j.val) = actionsAt (branch j).evidence (width j) := by
  unfold branchWords
  rw [label_index, Equiv.apply_symm_apply]

def expectedWord {original bound : Program} (caller : OpenAssembly original)
    (branch : (j : Fin 4) → Branch (reroot bound caller.slots[j]) j)
    (width : ∀ j, (branch j).evidence.trace.wireCount = 8) : List (GateAction 10) :=
  layout.word (actionsAt caller.selector caller.selectorWidth) (List.range 4)
    (fun j => branchWords branch width (SelectLayout.label j))

structure LinkedAssembly {original : Program} (caller : OpenAssembly original) (bound : Program) where
  link : ScopedSourceLink original bound []
  output : GateEvidence.Certificate bound
  outputWidth : output.trace.wireCount = 10
  declaredScale : readScale bound = .ok caller.scale
  branches : (j : Fin 4) → Branch (reroot bound caller.slots[j]) j
  branchWidths : ∀ j, (branches j).evidence.trace.wireCount = 8
  branchScales : ∀ j, (branches j).scale = 2
  word : ((actionsAt output outputWidth).filter fun step => !step.isZeroRotation) =
    ((expectedWord caller branches branchWidths).filter fun step => !step.isZeroRotation)

/-- Only the selector and branch columns are evaluated numerically. The full output
is lowered and compared as an instruction word, including any entry wrapper. -/
def certifyLinkedAssembly {original : Program} (caller : OpenAssembly original)
    (bound : Program) : Except String (LinkedAssembly caller bound) := do
  let link ← verifyScopedSourceLink original bound
  unless assembly bound caller.scale = .ok (caller.slots, caller.prepare) do
    throw "Bound LCHS changed the quadrature layout or normalization"
  unless (reroot bound caller.prepare).resolve = .ok caller.selector.trace do
    throw "Bound LCHS changed the selector gate word"
  if declaredScale : readScale bound = .ok caller.scale then
    let branches ← certifyBranches bound caller.slots
    if branchWidths : ∀ j : Fin 4, (branches j).evidence.trace.wireCount = 8 then
      if branchScales : ∀ j : Fin 4, (branches j).scale = 2 then
        let output ← GateEvidence.certify bound
        if outputWidth : output.trace.wireCount = 10 then
          if word : ((actionsAt output outputWidth).filter fun step => !step.isZeroRotation) =
              ((expectedWord caller branches branchWidths).filter fun step => !step.isZeroRotation) then
            return ⟨link, output, outputWidth, declaredScale, branches, branchWidths, branchScales, word⟩
          else throw "Bound LCHS gate word differs from PREPARE, SELECT, and inverse PREPARE"
        else throw "Expected two selector wires and eight branch wires"
      else throw "Bound LCHS changed a branch normalization"
    else throw "Bound LCHS changed a branch interface"
  else throw "Bound LCHS changed the output normalization"

private noncomputable def measuredCoefficient {original : Program} (caller : OpenAssembly original)
    (j : Fin 4) : ℝ :=
  (caller.scale : ℝ) * ‖matrixAt caller.selector caller.selectorWidth
    (SelectLayout.label j.val) (fun _ => false)‖ ^ 2 / 2

private theorem coefficient_error {original : Program} (caller : OpenAssembly original) (j : Fin 4) :
    ‖(measuredCoefficient caller j : ℂ) - staticLchsCoeff 1 4 j‖ ≤ (1 : ℝ) / 10^12 := by
  have bound := selector_weight_error caller.selector caller.scale 2 caller.positiveScale
    caller.smallScale j (caller.weights j)
  dsimp only at bound
  let p := ‖matrixAt caller.selector caller.selectorWidth
    (SelectLayout.label j.val) (fun _ => false)‖ ^ 2
  rw [← selectorAt_entry caller.selector caller.selectorWidth j] at bound
  have checked : |Real.pi * (caller.scale : ℝ) * p - (weightNumerator j : ℝ) * 2| ≤ (2 : ℝ) / 10^12 := by
    simpa only [Rat.cast_ofNat] using bound
  have eq : (Real.pi : ℂ) * ((measuredCoefficient caller j : ℂ) - staticLchsCoeff 1 4 j) =
      (((Real.pi * (caller.scale : ℝ) * p - (weightNumerator j : ℝ) * 2) / 2 : ℝ) : ℂ) := by
    rw [mul_sub, weight_eq]
    change (Real.pi : ℂ) * (((caller.scale : ℝ) * p / 2 : ℝ) : ℂ) -
        ((weightNumerator j : ℝ) : ℂ) =
      (((Real.pi * (caller.scale : ℝ) * p - (weightNumerator j : ℝ) * 2) / 2 : ℝ) : ℂ)
    push_cast
    ring
  have h := congrArg norm eq
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  have π : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (norm_nonneg _) π).trans (h.trans_le (by linarith))

private theorem coefficient_asSquare (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  exact mul_comm _ _

private theorem branch_block_bound {bound : Program} {j : Fin 4} (branch : Branch bound j)
    (scale : branch.scale = 2) : ‖branch.block‖ ≤ 2 := by
  rw [Branch.block, scale, norm_smul, Real.norm_eq_abs]
  norm_num only [Rat.cast_ofNat, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have frame := basisFrame_isIsometry branch.embed
  exact mul_le_of_le_one_right (by norm_num)
    ((compress_norm_le frame frame _).trans (unitary_norm_le_one branch.evidence.sound.2))

private theorem exact_output_block {original bound : Program} {caller : OpenAssembly original}
    (cert : LinkedAssembly caller bound) :
    (caller.scale : ℝ) • compress (basisFrame outputFrame)
        (matrixAt cert.output cert.outputWidth) (basisFrame outputFrame) =
      ∑ j : Fin 4, (measuredCoefficient caller j : ℂ) • (cert.branches j).block := by
  have word := congrArg (fun xs : List (GateAction 10) => wordMatrix (xs.map GateAction.matrix)) cert.word
  simp only [GateAction.word_without_zero] at word
  have result := layout.word_matrix (actionsAt caller.selector caller.selectorWidth) (List.range 4)
    (branchWords cert.branches cert.branchWidths)
    (by decide) labels_complete
  change matrixAt cert.output cert.outputWidth = _ at word
  rw [word, expectedWord, result, outputFrame, SelectLayout.compress_lift, selectPrepare_compress]
  rw [← (orderedBitsIndex 2).symm.sum_comp]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← label_index, coefficient_asSquare, branchAt_block (cert.branches j) (cert.branchWidths j),
    cert.branchScales j]
  rw [branchWords_label cert.branches cert.branchWidths j]
  simp only [Matrix.mulVec, dotProduct, Ket]
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp only [ite_true, mul_one, measuredCoefficient, matrixAt]
    ext r c
    simp only [Matrix.smul_apply, Complex.real_smul, Rat.cast_ofNat, smul_eq_mul]
    push_cast
    ring
  · intro b _ diff
    simp [diff]
  · simp

theorem LinkedAssembly.assembly_error {original bound : Program} {caller : OpenAssembly original}
    (cert : LinkedAssembly caller bound) :
    ‖(caller.scale : ℝ) • compress (basisFrame outputFrame)
        (matrixAt cert.output cert.outputWidth) (basisFrame outputFrame) -
      ∑ j : Fin 4, staticLchsCoeff 1 4 j • (cert.branches j).block‖ ≤ (1 : ℝ) / 10^10 := by
  rw [exact_output_block cert, ← Finset.sum_sub_distrib]
  trans ∑ j : Fin 4, ‖(measuredCoefficient caller j : ℂ) • (cert.branches j).block -
    staticLchsCoeff 1 4 j • (cert.branches j).block‖
  · exact norm_sum_le _ _
  · trans ∑ _ : Fin 4, ((1 : ℝ) / 10^12) * 2
    · apply Finset.sum_le_sum
      intro j _
      rw [← sub_smul, norm_smul]
      exact mul_le_mul (coefficient_error caller j) (branch_block_bound _ (cert.branchScales j))
        (norm_nonneg _) (by positivity)
    · norm_num

theorem LinkedAssembly.sound {original bound : Program} {caller : OpenAssembly original}
    (cert : LinkedAssembly caller bound) :
    cert.link.exposed = cert.link.closed.hideSlots caller.slots.toList ∧
    bound.matrix (fun _ => none) = .ok ⟨10, matrixAt cert.output cert.outputWidth⟩ ∧
    BlockEncoding (staticLchsQuadrature sampleL sampleH (1 / 8) 1 4)
      (matrixAt cert.output cert.outputWidth) (basisFrame outputFrame) (basisFrame outputFrame)
      (caller.scale : ℝ) (1 / 50) := by
  have graph : cert.link.caller = caller.graph :=
    Except.ok.inj (cert.link.source_resolved.symm.trans caller.resolved)
  have retained := cert.link.checked
  rw [graph, caller.slotsMatch] at retained
  obtain ⟨evaluated, unitary⟩ := matrixAt_sound cert.output cert.outputWidth
  refine ⟨retained, evaluated, unitary, basisFrame_isIsometry _, basisFrame_isIsometry _,
    by exact_mod_cast caller.positiveScale, by norm_num, ?_⟩
  rw [exact_output_block cert, staticLchsQuadrature]
  refine (weighted_blocks_error (staticLchsCoeff 1 4)
    (fun j => (measuredCoefficient caller j : ℂ)) _
    (fun j => (cert.branches j).block) (fun _ => 3 / 200) (fun _ => 1 / 10^12) (fun _ => 2)
    (fun j => (cert.branches j).sound.2) (fun j => (norm_sub_rev ..).le.trans
      (coefficient_error caller j))
    (fun j => branch_block_bound _ (cert.branchScales j))).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  norm_num
  nlinarith [weight_mass_le]

end OracqVerify.Verification.LCHS
