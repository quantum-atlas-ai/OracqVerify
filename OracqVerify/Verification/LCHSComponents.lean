module

public import OracqVerify.Verification.LCHSReplacement

/-! Component validation for the four-node, noncommuting LCHS example. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.LCHS

open Lean RIR Matrix Polynomial
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.CoherentSim.FactorialTaylor Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Foundations.OperatorErrors.OperatorError
open scoped Matrix.Norms.L2Operator

def node (j : Fin 4) : ℚ := -1 + (j.val : ℚ) / 2

def weightNumerator (j : Fin 4) : ℚ := (1 / 2) / (1 + (node j) ^ 2)

def nodeEntry (j : Fin 4) (row col : Bool) : Gaussian :=
  let k := node j
  if row = col then
    let d := (if row then 1 / 2 else 3 / 2) * k
    ⟨1 - (d ^ 2 + 1 / 16) / 128, -d / 8⟩
  else ⟨-k / 256, -1 / 32⟩

noncomputable def nodeTaylor (j : Fin 4) : Matrix Bool Bool ℂ :=
  aeval (sampleH + staticLchsGrid 1 4 j • sampleL) (exponentialTaylorPolynomial (1 / 8) 3)

set_option maxHeartbeats 4000000 in
theorem nodeTaylor_entry (j : Fin 4) (row col : Bool) :
    nodeTaylor j row col = gaussianComplex (nodeEntry j row col) := by
  fin_cases j <;> cases row <;> cases col <;> apply Complex.ext <;>
    norm_num [nodeTaylor, nodeEntry, node, aeval_exponentialTaylorPolynomial, staticLchsGrid,
      Finset.sum_range_succ, sampleH, sampleL, Fintype.sum_bool, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, pow_two, PauliX, permMatrix, Complex.mul_re, Complex.mul_im]

def signalView (offset count : Nat) : Ref :=
  ⟨⟨.bits, count⟩, if count = 0 then [] else [⟨"signal", offset, count⟩]⟩

def reroot (program : Program) (name : String) : Program := { program with entry := name }

def numericAttribute (module_ : RIR.Module) (name : String) : Except String ℚ := do
  let some (.num value) := module_.attributes.lookup name | throw s!"Missing numeric {name}"
  return rationalAngle value

def branchCall (program : Program) (signalWires expected : Nat) (step : Instruction) :
    Except String String := do
  let .control guard value [.gphase phase, .call name args []] := step |
    throw "Expected one phased SELECT call per LCHS node"
  unless guard == signalView 0 2 && value == expected && rationalAngle phase == 0 do
    throw "Wrong LCHS selector, index, or coefficient phase"
  let branch ← lookupModule program name
  let [target, signal] := branch.registers | throw "Expected LCHS branch target and signal"
  unless target == ⟨"target", ⟨.bits, 1⟩⟩ && signal == ⟨"signal", ⟨.bits, signal.type.width⟩⟩ &&
      signal.type.width ≤ signalWires && args == [bitsRef "target" 1, signalView 2 signal.type.width] do
    throw "Wrong target or signal layout in LCHS SELECT"
  return name

def assembly (program : Program) (scale : ℚ) : Except String (Vector String 4 × String) := do
  let entry ← lookupModule program program.entry
  let some (.str nodes) := entry.attributes.lookup "quadrature_nodes" |
    throw "Expected LCHS quadrature nodes"
  let .arr grid ← Json.parse nodes | throw "Expected a list of LCHS quadrature nodes"
  let grid ← grid.toList.mapM fun value =>
    match value with
    | .num n => .ok (rationalAngle n)
    | _ => .error "Expected a numeric LCHS node"
  unless grid == (List.finRange 4).map node && (← numericAttribute entry "branch_count") == 4 do
    throw "Wrong LCHS quadrature node order"
  let [target, signal] := entry.registers | throw "Expected LCHS target and signal"
  unless target == ⟨"target", ⟨.bits, 1⟩⟩ && 2 ≤ signal.type.width do
    throw "Wrong LCHS root register layout"
  let some [.call _ initialArgs [], .call outer outerArgs []] := entry.body |
    throw "Expected initial preparation followed by one LCHS LCU"
  unless initialArgs == [bitsRef "target" 1, signalView 0 0] &&
      outerArgs == [bitsRef "target" 1, signalView 0 signal.type.width] do
    throw "Wrong LCHS wrapper register placement"
  let lcu ← lookupModule program outer
  unless lcu.registers == entry.registers && (← numericAttribute lcu "be_alpha") == scale do
    throw "LCHS outer scale or interface disagrees"
  let some [.call prep prepareArgs [], first, second, third, fourth, .adjoint [.call unprep unprepareArgs []]]
      := lcu.body | throw "Expected preparation, four LCHS branches, and inverse preparation"
  unless prep == unprep && prepareArgs == [signalView 0 2, signalView 0 0] &&
      prepareArgs == unprepareArgs do
    throw "LCHS preparation and its adjoint use different selector layouts"
  let read := branchCall program (signal.type.width - 2)
  return (#[← read 0 first, ← read 1 second, ← read 2 third, ← read 3 fourth].toVector, prep)

structure Branch (program : Program) (j : Fin 4) where
  evidence : GateEvidence.Certificate program
  width : 0 < evidence.trace.wireCount
  scale : ℚ
  declared : (lookupModule program program.entry >>= (numericAttribute · "be_alpha")) = .ok scale
  positiveScale : 0 < scale
  smallScale : scale ≤ 2
  entries : Entries
  computed : entries = scaledEntries evidence scale
  approximation : ∀ row col : Bool,
    GateEvidence.l1 (nodeEntry j row col - entries.get row col) ≤ 1 / 200

def certifyBranch (program : Program) (j : Fin 4) : Except String (Branch program j) := do
  let evidence ← GateEvidence.certify program
  match declared : (lookupModule program program.entry >>= (numericAttribute · "be_alpha")) with
  | .error reason => throw reason
  | .ok scale =>
    if width : 0 < evidence.trace.wireCount then
      if positive : 0 < scale then
        if small : scale ≤ 2 then
          let entries := scaledEntries evidence scale
          if checked : ∀ row col : Bool, GateEvidence.l1 (nodeEntry j row col - entries.get row col) ≤ 1 / 200 then
            return ⟨evidence, width, scale, declared, positive, small, entries, rfl, checked⟩
          else throw s!"LCHS branch {j.val} fails its Hamiltonian approximation budget"
        else throw "LCHS branch scale exceeds two"
      else throw "LCHS branch scale must be positive"
    else throw "LCHS branch target is missing"

def Branch.embed {program : Program} {j : Fin 4} (cert : Branch program j) :
    Bool ↪ Reg cert.evidence.trace.wireCount where
  toFun := GateEvidence.zeroSignal _
  inj' := by
    intro a b same
    exact congrFun same ⟨0, cert.width⟩

noncomputable def Branch.block {program : Program} {j : Fin 4} (cert : Branch program j) :
    Matrix Bool Bool ℂ :=
  (cert.scale : ℝ) • compress (basisFrame cert.embed) cert.evidence.matrix (basisFrame cert.embed)

theorem Branch.rounding {program : Program} {j : Fin 4} (cert : Branch program j) (row col : Bool) :
    ‖cert.block row col - gaussianComplex (cert.entries.get row col)‖ ≤ (2 : ℝ) / 10^20 := by
  rw [Branch.block, Matrix.smul_apply, basisFrame_compress, cert.computed, scaledEntries_apply,
    scaledEntry, map_mul, gaussianComplex_ofReal, ← Complex.real_smul, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by exact_mod_cast cert.positiveScale)]
  have small : (cert.scale : ℝ) ≤ 2 := by exact_mod_cast cert.smallScale
  change (cert.scale : ℝ) *
    ‖cert.evidence.matrix (cert.embed row) (cert.embed col) -
      gaussianComplex (cert.evidence.column (cert.embed col) (cert.embed row))‖ ≤ _
  calc
    _ ≤ 2 * (1 / (10 : ℝ)^20) :=
      mul_le_mul small (cert.evidence.entry_error _ _) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem Branch.sound {program : Program} {j : Fin 4} (cert : Branch program j) :
    program.matrix (fun _ => none) = .ok ⟨cert.evidence.trace.wireCount, cert.evidence.matrix⟩ ∧
    ‖hamiltonianEvolution (sampleH + staticLchsGrid 1 4 j • sampleL) (1 / 8) - cert.block‖ ≤
      (3 : ℝ) / 200 := by
  refine ⟨cert.evidence.sound.1, ?_⟩
  have entry (row col : Bool) :
      ‖(nodeTaylor j - cert.block) row col‖ ≤ (51 : ℝ) / 10000 := by
    rw [Matrix.sub_apply, nodeTaylor_entry]
    have checked := (GateEvidence.norm_le_l1
      (nodeEntry j row col - cert.entries.get row col)).trans
      (show (GateEvidence.l1 _ : ℝ) ≤ 1 / 200 by
        have numeric := (Rat.cast_le (K := ℝ)).mpr (cert.approximation row col)
        norm_num at numeric ⊢
        exact numeric)
    rw [map_sub] at checked
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add checked ((norm_sub_rev ..).le.trans (cert.rounding row col)))).trans (by norm_num)
  have numeric : ‖nodeTaylor j - cert.block‖ ≤ (11 : ℝ) / 1000 := by
    refine (boolMatrixNorm _ (diag := 51 / 10000) (off := 51 / 10000) (by norm_num)
      (by norm_num) (fun row => entry row row) ?_).trans (by norm_num)
    intro row
    cases row
    · exact entry false true
    · exact entry true false
  exact ((norm_sub_le_norm_sub_add_norm_sub _ (nodeTaylor j) _).trans
    (add_le_add ((norm_sub_rev ..).le.trans (artifact_nodeTaylor j)) numeric)).trans (by norm_num)

def selectorEntry {program : Program} (prep : GateEvidence.Certificate program) (j : Fin 4) :
    Gaussian :=
  prep.column (fun _ => false) (fun wire => Nat.testBit j.val wire.val)

structure ComponentContracts (program : Program) where
  output : ScaledBlock program
  names : Vector String 4
  prepare : String
  wiring : assembly program output.scale = .ok (names, prepare)
  branches : (j : Fin 4) → Branch (reroot program names[j]) j
  selector : GateEvidence.Certificate (reroot program prepare)
  selectorWidth : selector.trace.wireCount = 2
  weights : ∀ j : Fin 4,
    |rationalPiLower * output.scale * GateEvidence.normSquare (selectorEntry selector j) -
      weightNumerator j * (branches j).scale| ≤ 1 / 10^12
structure Components (program : Program) extends ComponentContracts program where
  composition : ∀ row col : Bool, GateEvidence.l1
    ((⟨rationalPiLower, 0⟩ : Gaussian) * output.entries.get row col -
      ∑ j : Fin 4, (⟨weightNumerator j, 0⟩ : Gaussian) * (branches j).entries.get row col) ≤ 1 / 10^12

def certifyBranches (program : Program) (names : Vector String 4) :
    Except String ((j : Fin 4) → Branch (reroot program names[j]) j) := do
  let first ← certifyBranch (reroot program names[0]) 0
  let second ← certifyBranch (reroot program names[1]) 1
  let third ← certifyBranch (reroot program names[2]) 2
  let fourth ← certifyBranch (reroot program names[3]) 3
  return Fin.cases first (Fin.cases second (Fin.cases third (Fin.cases fourth (fun i => Fin.elim0 i))))

def certifyComposition {program : Program} (contracts : ComponentContracts program) :
    Except String (Components program) :=
  if composition : ∀ row col : Bool, GateEvidence.l1
      ((⟨rationalPiLower, 0⟩ : Gaussian) * contracts.output.entries.get row col -
        ∑ j : Fin 4, (⟨weightNumerator j, 0⟩ : Gaussian) * (contracts.branches j).entries.get row col) ≤ 1 / 10^12 then
    .ok ⟨contracts, composition⟩
  else .error "LCHS output disagrees with the weighted sum of its decoded branches"

theorem certifyComposition_contracts {program : Program} {contracts : ComponentContracts program}
    {components : Components program} (checked : certifyComposition contracts = .ok components) :
    components.toComponentContracts = contracts := by
  unfold certifyComposition at checked
  split at checked
  · cases checked
    rfl
  · cases checked

def certifyComponents (program : Program) : Except String (Components program) := do
  let output ← certifyScaledBlock program
  match wiring : assembly program output.scale with
  | .error reason => throw reason
  | .ok (names, prepare) =>
    let branches ← certifyBranches program names
    let selector ← GateEvidence.certify (reroot program prepare)
    if selectorWidth : selector.trace.wireCount = 2 then
      if weights : ∀ j : Fin 4,
          |rationalPiLower * output.scale * GateEvidence.normSquare (selectorEntry selector j) -
            weightNumerator j * (branches j).scale| ≤ 1 / 10^12 then
        certifyComposition ⟨output, names, prepare, wiring, branches, selector, selectorWidth, weights⟩
      else throw "LCHS selector probabilities disagree with the Cauchy weights"
    else throw "Expected a two-wire LCHS selector preparation"


theorem weight_eq (j : Fin 4) :
    (Real.pi : ℂ) * staticLchsCoeff 1 4 j = ((weightNumerator j : ℝ) : ℂ) := by
  rw [staticLchsCoeff, ← Complex.ofReal_mul]
  congr 1
  fin_cases j <;> norm_num [staticLchsGrid, weightNumerator, node] <;>
    field_simp [Real.pi_ne_zero] <;> ring

private theorem weight_le_one (j : Fin 4) : ‖((weightNumerator j : ℝ) : ℂ)‖ ≤ 1 := by
  fin_cases j <;> norm_num [weightNumerator, node, Complex.norm_real, Real.norm_eq_abs]

private theorem piRounding :
    ‖(Real.pi : ℂ) - ((rationalPiLower : ℝ) : ℂ)‖ ≤ 1 / 10^20 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have lo := Real.pi_gt_d20
  have hi := Real.pi_lt_d20
  norm_num [rationalPiLower] at lo hi ⊢
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The weighted success blocks of the branches selected by the serialized LCU. -/
noncomputable def Components.weighted {program : Program} (cert : Components program) :
    Matrix Bool Bool ℂ :=
  ∑ j : Fin 4, staticLchsCoeff 1 4 j • (cert.branches j).block

/-- Compare the actual outer block to the weighted sum of the actual selected branch blocks. -/
theorem Components.assembly_error {program : Program} (cert : Components program) :
    ‖cert.output.block - cert.weighted‖ ≤ (1 : ℝ) / 10^10 := by
  have entry (row col : Bool) : ‖(cert.output.block - cert.weighted) row col‖ ≤ (2 : ℝ) / 10^12 := by
    let p : ℂ := ((rationalPiLower : ℝ) : ℂ)
    let g := gaussianComplex (cert.output.entries.get row col)
    let u := cert.output.block row col
    let concrete := fun j : Fin 4 => (cert.branches j).block row col
    let approx := fun j : Fin 4 => gaussianComplex ((cert.branches j).entries.get row col)
    let weight := fun j : Fin 4 => ((weightNumerator j : ℝ) : ℂ)
    have hu : ‖u‖ ≤ 1 := by
      unfold u ScaledBlock.block
      rw [Matrix.smul_apply, basisFrame_compress, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by exact_mod_cast cert.output.positiveScale)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast cert.output.smallScale)).trans
        (entry_norm_bound_of_unitary cert.output.evidence.sound.2 _ _)
    have hp : ‖p‖ ≤ 4 := by norm_num [p, rationalPiLower, Complex.norm_real, Real.norm_eq_abs]
    have errOut : ‖(Real.pi : ℂ) * u - p * g‖ ≤ (5 : ℝ) / 10^20 := by
      have identity : (Real.pi : ℂ) * u - p * g =
          ((Real.pi : ℂ) - p) * u + p * (u - g) := by ring
      rw [identity]
      refine (norm_add_le ..).trans ?_
      rw [norm_mul, norm_mul]
      have first := mul_le_mul (piRounding) hu (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10^20)
      have second := mul_le_mul hp (cert.output.entry_error row col) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have errBranches : ‖(∑ j : Fin 4, weight j * approx j) - ∑ j : Fin 4, weight j * concrete j‖
        ≤ (8 : ℝ) / 10^20 := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ _ : Fin 4, (2 : ℝ) / 10^20 := by
          apply Finset.sum_le_sum
          intro j _
          rw [← mul_sub, norm_mul, norm_sub_rev]
          exact (mul_le_of_le_one_left (norm_nonneg _) (weight_le_one j)).trans ((cert.branches j).rounding row col)
        _ = _ := by norm_num
    have errCheck : ‖p * g - ∑ j : Fin 4, weight j * approx j‖ ≤ (1 : ℝ) / 10^12 := by
      let diff : Gaussian := (⟨rationalPiLower, 0⟩ : Gaussian) * cert.output.entries.get row col -
        ∑ j : Fin 4, (⟨weightNumerator j, 0⟩ : Gaussian) * (cert.branches j).entries.get row col
      have norm := (GateEvidence.norm_le_l1 diff).trans
        (show (GateEvidence.l1 diff : ℝ) ≤ 1 / 10^12 by
          have numeric := (Rat.cast_le (K := ℝ)).mpr (cert.composition row col)
          norm_num at numeric ⊢
          exact numeric)
      simpa only [diff, map_sub, map_mul, map_sum, gaussianComplex_ofReal, p, g, weight, approx] using norm
    have scaled : ‖(Real.pi : ℂ) * (cert.output.block - cert.weighted) row col‖ ≤
        (2 : ℝ) / 10^12 := by
      rw [Matrix.sub_apply, mul_sub, Components.weighted]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc, weight_eq]
      have err := (norm_sub_le_norm_sub_add_norm_sub _ (p * g) _).trans
        (add_le_add errOut ((norm_sub_le_norm_sub_add_norm_sub _ (∑ j : Fin 4, weight j * approx j) _).trans
          (add_le_add errCheck errBranches)))
      exact err.trans (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at scaled
    exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)).trans scaled
  exact (norm_bool_matrix_le _ (by norm_num) entry).trans (by norm_num)

/-- A single assembly rule combines any separate estimates for the selected blocks. -/
theorem quadrature_of_components (output : Matrix Bool Bool ℂ)
    (blocks : Fin 4 → Matrix Bool Bool ℂ) (errors : Fin 4 → ℝ) (δ : ℝ)
    (branches : ∀ j, ‖hamiltonianEvolution (sampleH + staticLchsGrid 1 4 j • sampleL) (1 / 8) -
      blocks j‖ ≤ errors j)
    (assembly : ‖output - ∑ j : Fin 4, staticLchsCoeff 1 4 j • blocks j‖ ≤ δ) :
    ‖staticLchsQuadrature sampleL sampleH (1 / 8) 1 4 - output‖ ≤
      (∑ j : Fin 4, ‖staticLchsCoeff 1 4 j‖ * errors j) + δ := by
  let weighted := ∑ j : Fin 4, staticLchsCoeff 1 4 j • blocks j
  have sumBound : ‖staticLchsQuadrature sampleL sampleH (1 / 8) 1 4 - weighted‖ ≤
      ∑ j : Fin 4, ‖staticLchsCoeff 1 4 j‖ * errors j := by
    unfold staticLchsQuadrature weighted
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_left (branches j) (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ weighted _).trans
    (add_le_add sumBound ((norm_sub_rev ..).le.trans assembly))

/-- The branch workspaces may differ. The common estimate is on the logical target. -/
theorem Components.quadrature_error {program : Program} (cert : Components program) :
    ‖staticLchsQuadrature sampleL sampleH (1 / 8) 1 4 - cert.output.block‖ ≤ (2 : ℝ) / 100 := by
  refine (quadrature_of_components cert.output.block
    (fun j => (cert.branches j).block) (fun _ => 3 / 200) (1 / 10^10)
    (fun j => (cert.branches j).sound.2) cert.assembly_error).trans ?_
  rw [← Finset.sum_mul]
  nlinarith [weight_mass_le]

/-- The physical selector amplitudes carry the Cauchy weights multiplied by the
branch normalizations, within the checked tolerance. -/
theorem selector_weight_error {program : Program} (selector : GateEvidence.Certificate program)
    (scale branchScale : ℚ) (positive : 0 < scale) (small : scale ≤ 1) (j : Fin 4)
    (weights : |rationalPiLower * scale * GateEvidence.normSquare (selectorEntry selector j) -
      weightNumerator j * branchScale| ≤ 1 / 10^12) :
    let amplitude := selector.matrix (fun wire => Nat.testBit j.val wire.val) (fun _ => false)
    |Real.pi * (scale : ℝ) * ‖amplitude‖ ^ 2 -
      (weightNumerator j : ℝ) * (branchScale : ℝ)| ≤ (2 : ℝ) / 10^12 := by
  dsimp only
  let u := selector.matrix (fun wire => Nat.testBit j.val wire.val) (fun _ => false)
  let g := gaussianComplex (selectorEntry selector j)
  let p : ℝ := rationalPiLower
  let α : ℝ := scale
  have round : ‖u - g‖ ≤ (1 : ℝ) / 10^20 := selector.entry_error _ _
  have hu : ‖u‖ ≤ 1 := entry_norm_bound_of_unitary selector.sound.2 _ _
  have close := (abs_norm_sub_norm_le u g).trans round
  have hg : ‖g‖ ≤ 2 := by
    have bound := (abs_le.mp close).1
    linarith
  have squares : |‖u‖ ^ 2 - ‖g‖ ^ 2| ≤ (3 : ℝ) / 10^20 := by
    rw [show ‖u‖ ^ 2 - ‖g‖ ^ 2 = (‖u‖ - ‖g‖) * (‖u‖ + ‖g‖) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ + ‖g‖)]
    exact (mul_le_mul close (show ‖u‖ + ‖g‖ ≤ 3 by linarith) (by positivity) (by norm_num)).trans_eq (by ring)
  have πdiff : |Real.pi - p| ≤ (1 : ℝ) / 10^20 := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using piRounding
  have scaleBound : |α| ≤ 1 := by
    change |(scale : ℝ)| ≤ 1
    rw [abs_of_pos (by exact_mod_cast positive)]
    exact_mod_cast small
  have hp : |p| ≤ 4 := by norm_num [p, rationalPiLower]
  let target : ℝ := (weightNumerator j : ℝ) * (branchScale : ℝ)
  have checked : |p * α * ‖g‖ ^ 2 - target| ≤ (1 : ℝ) / 10^12 := by
    rw [GateEvidence.norm_square]
    have numeric := (Rat.cast_le (K := ℝ)).mpr weights
    push_cast at numeric
    exact numeric
  change |Real.pi * α * ‖u‖ ^ 2 - target| ≤ _
  rw [show Real.pi * α * ‖u‖ ^ 2 - target =
      (Real.pi - p) * α * ‖u‖ ^ 2 + p * α * (‖u‖ ^ 2 - ‖g‖ ^ 2) +
      (p * α * ‖g‖ ^ 2 - target) by ring]
  refine (abs_add_le ..).trans ((add_le_add (abs_add_le ..) (le_refl _)).trans ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ ^ 2)]
  have errPi : |Real.pi - p| * |α| * ‖u‖ ^ 2 ≤ (1 : ℝ) / 10^20 := by
    have h : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    exact (mul_le_of_le_one_right (by positivity) h).trans
      ((mul_le_of_le_one_right (by positivity) scaleBound).trans πdiff)
  have errSquare : |p| * |α| * |‖u‖ ^ 2 - ‖g‖ ^ 2| ≤ (12 : ℝ) / 10^20 := by
    have h := mul_le_mul ((mul_le_of_le_one_right (abs_nonneg p) scaleBound).trans hp) squares
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  linarith


theorem Components.selector_error {program : Program} (cert : Components program) (j : Fin 4) :
    let amplitude := cert.selector.matrix (fun wire => Nat.testBit j.val wire.val) (fun _ => false)
    |Real.pi * (cert.output.scale : ℝ) * ‖amplitude‖ ^ 2 -
      (weightNumerator j : ℝ) * ((cert.branches j).scale : ℝ)| ≤ (2 : ℝ) / 10^12 :=
  selector_weight_error cert.selector cert.output.scale (cert.branches j).scale
    cert.output.positiveScale cert.output.smallScale j (cert.weights j)

theorem Components.continuum_error {program : Program} (cert : Components program) :
    ‖staticNonunitaryEvolution sampleL sampleH (1 / 8) - cert.output.block‖ ≤
      (1 : ℝ) / 50 + quadratureError sampleL (1 / 8) 1 4 := by
  have err := static_noncommuting_lchs_quadrature_error Bool sampleL sampleH (1 / 8) 1 4
    sampleL_posSemidef sampleH_hermitian (by norm_num) (by decide) (by decide)
  rw [norm_sub_rev] at err
  have bound := (norm_sub_le_norm_sub_add_norm_sub _
    (staticLchsQuadrature sampleL sampleH (1 / 8) 1 4) _).trans
    (add_le_add err cert.quadrature_error)
  rw [add_comm]
  simpa only [quadratureError, show (2 : ℝ) / 100 = 1 / 50 by norm_num] using bound

end OracqVerify.Verification.LCHS
