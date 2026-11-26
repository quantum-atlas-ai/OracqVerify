module

public import OracqVerify.Verification.LCHS
public meta import OracqVerify.RIR.Resolve
public meta import Lean.Elab.Term

/-! The decoded noncommuting LCHS artifact and its first Taylor branch. -/

set_option warningAsError true

public section

namespace OracqVerify.Verification.LCHS

open RIR
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator ComplexOrder

private meta def readTraces : Except String (ResolvedProgram × ResolvedProgram) := do
  let program ← Program.fromJson (← Lean.Json.parse
    (include_str "../../fixtures/lchs.noncommuting.json"))
  let entry ← lookupModule program program.entry
  let some [_, .call outerName ..] := entry.body | throw "Unexpected LCHS entry body"
  let outer ← lookupModule program outerName
  let some (.call .. :: .control _ 0 [.gphase _, .call branchName ..] :: _) := outer.body
    | throw "Missing the first LCHS SELECT branch"
  let branch ← lookupModule program branchName
  unless (entry.registers = [⟨"target", ⟨.bits, 1⟩⟩, ⟨"signal", ⟨.bits, 8⟩⟩]) ∧
      (branch.registers = [⟨"target", ⟨.bits, 1⟩⟩, ⟨"signal", ⟨.bits, 6⟩⟩]) do
    throw "Unexpected LCHS entry or branch basis layout"
  let scale ← Lean.Json.parse "1.24267578125"
  let outerScale ← Lean.Json.parse "0.551563578415394"
  unless entry.attributes.lookup "evolution_alpha" == some outerScale do
    throw "Unexpected outer LCHS normalization"
  unless branch.attributes.lookup "algorithm" == some (.str "truncated_taylor_hamiltonian_function") &&
      branch.attributes.lookup "be_alpha" == some scale do
    throw "Unexpected Taylor branch kind or normalization"
  return (← program.resolve, ← ({ program with entry := branchName } : Program).resolve)

open Lean in
private meta def quoteGate : UnaryGate → Expr
  | .h => mkConst ``UnaryGate.h
  | .x => mkConst ``UnaryGate.x
  | .z => mkConst ``UnaryGate.z
  | .ry a => mkApp (mkConst ``UnaryGate.ry)
      (mkApp2 (mkConst ``JsonNumber.mk) (toExpr a.mantissa) (toExpr a.exponent))

open Lean in
private meta def quoteStep : ResolvedInstruction → Elab.Term.TermElabM Expr
  | .unary gate wires => pure (mkApp2 (mkConst ``ResolvedInstruction.unary)
      (quoteGate gate) (toExpr wires))
  | .gphase a => pure (mkApp (mkConst ``ResolvedInstruction.gphase)
      (mkApp2 (mkConst ``JsonNumber.mk) (toExpr a.mantissa) (toExpr a.exponent)))
  | .controlled g step => do
    let guard := mkApp2 (mkConst ``Guard.mk) (toExpr g.wires) (toExpr g.value)
    return mkApp2 (mkConst ``ResolvedInstruction.controlled) guard (← quoteStep step)
  | .adjoint step => return mkApp (mkConst ``ResolvedInstruction.adjoint) (← quoteStep step)
  | _ => throwError "Expected a gate-only trace in the LCHS fixture"

open Lean in
private meta def quoteTrace (p : ResolvedProgram) : Elab.Term.TermElabM Expr := do
  let steps ← p.instructions.mapM quoteStep
  let list ← Meta.mkListLit (mkConst ``ResolvedInstruction) steps
  return mkApp2 (mkConst ``ResolvedProgram.mk) (toExpr p.wireCount) list

open Lean in
local elab "decodeLchsFixture" branch:ident : term => do
  match readTraces with
  | .ok (program, first) =>
    if branch.getId == `first then quoteTrace first else quoteTrace program
  | .error message => throwError "Invalid LCHS fixture: {message}"

/-- The full program resolved from the pinned Oracq-generated JSON. -/
@[expose] def artifactTrace : ResolvedProgram := decodeLchsFixture full

/-- The first SELECT branch re-rooted in the same serialized module graph. -/
@[expose] def firstBranchTrace : ResolvedProgram := decodeLchsFixture first

theorem artifact_wireCount : artifactTrace.wireCount = 9 := rfl
theorem firstBranch_wireCount : firstBranchTrace.wireCount = 7 := rfl

/-- Place a one-bit target on physical wire zero and clear all signal bits. -/
@[expose] def zeroSignal (n : Nat) : Bool ↪ Reg (n + 1) where
  toFun bit wire := if wire.val = 0 then bit else false
  inj' := by
    intro row col h
    simpa using congrFun h (0 : Fin (n + 1))

private theorem artifact_gates :
    artifactTrace.instructions.all (ResolvedInstruction.isUnitaryGate artifactTrace.wireCount) =
      true := by decide

private theorem firstBranch_gates :
    firstBranchTrace.instructions.all
      (ResolvedInstruction.isUnitaryGate firstBranchTrace.wireCount) = true := by decide

theorem artifact_matrix :
    ∃ u : WireMatrix 9, artifactTrace.matrix (fun _ => none) = .ok u ∧ u ∈ unitaryGroup (Reg 9) ℂ :=
  artifactTrace.gateMatrix_exists (fun _ => none) artifact_gates

theorem firstBranch_matrix :
    ∃ u : WireMatrix 7, firstBranchTrace.matrix (fun _ => none) = .ok u ∧ u ∈ unitaryGroup (Reg 7) ℂ :=
  firstBranchTrace.gateMatrix_exists (fun _ => none) firstBranch_gates

/-- The normalization recorded by Oracq for the first Taylor branch. -/
@[expose] noncomputable def firstBranchScale : ℝ := 2545 / 2048

/-- The exact scaled success block of the serialized first branch, indexed just by target bits. -/
@[expose] noncomputable def firstBranchBlock (u : WireMatrix 7) : Matrix Bool Bool ℂ :=
  firstBranchScale • (fun row col => u (zeroSignal 6 row) (zeroSignal 6 col))

theorem firstBranch_blockEncoding :
    ∃ u : WireMatrix 7, firstBranchTrace.matrix (fun _ => none) = .ok u ∧
      BlockEncoding (firstBranchBlock u) u (basisFrame (zeroSignal 6))
        (basisFrame (zeroSignal 6)) firstBranchScale 0 := by
  obtain ⟨u, hm, hu⟩ := firstBranch_matrix
  refine ⟨u, hm, hu, basisFrame_isIsometry _, basisFrame_isIsometry _,
    by norm_num [firstBranchScale], le_rfl, ?_⟩
  have hc : compress (basisFrame (zeroSignal 6)) u (basisFrame (zeroSignal 6)) =
      (fun row col => u (zeroSignal 6 row) (zeroSignal 6 col)) := by
    ext row col
    exact basisFrame_compress (zeroSignal 6) u row col
  have hscaled : firstBranchBlock u =
      firstBranchScale • compress (basisFrame (zeroSignal 6)) u (basisFrame (zeroSignal 6)) :=
    congrArg (firstBranchScale • ·) hc.symm
  rw [← hscaled, sub_self, norm_zero]

/-- At node minus one, the Hamiltonian is `(1/4)X - I - (1/2)Z`. -/
@[expose] noncomputable def firstBranchCoefficients : Fin 3 → ℝ := ![1 / 4, -1, -(1 / 2)]

@[expose] noncomputable def firstBranchTerms : Fin 3 → Matrix Bool Bool ℂ := ![PauliX, 1, PauliZ]

@[expose] noncomputable def firstBranchHamiltonian : Matrix Bool Bool ℂ :=
  ∑ j, (firstBranchCoefficients j : ℂ) • firstBranchTerms j

@[expose] noncomputable def firstBranchTaylor : Matrix Bool Bool ℂ :=
  aeval firstBranchHamiltonian (exponentialTaylorPolynomial (1 / 8) 3)

/-- The analytic Taylor remainder for this branch adds at most one third to an error
certificate for the decoded polynomial block. -/
theorem firstBranch_evolution {u : WireMatrix 7} {δ : ℝ}
    (hm : firstBranchTrace.matrix (fun _ => none) = .ok u)
    (hδ : ‖firstBranchTaylor - firstBranchBlock u‖ ≤ δ) :
    BlockEncoding (hamiltonianEvolution firstBranchHamiltonian (1 / 8)) u
      (basisFrame (zeroSignal 6)) (basisFrame (zeroSignal 6)) firstBranchScale (δ + 1 / 3) := by
  obtain ⟨v, hv, hExact⟩ := firstBranch_blockEncoding
  rw [hm] at hv
  cases hv
  have hPolynomial := hExact.perturb ((norm_nonneg _).trans hδ) hδ
  rw [zero_add] at hPolynomial
  have hTerms : ∀ j, firstBranchTerms j ∈ unitaryGroup Bool ℂ := by
    intro j
    fin_cases j
    · exact pauliX_unitary
    · exact (unitaryGroup _ _).one_mem
    · exact pauliZ_unitary
  have hStrength : (∑ j, |firstBranchCoefficients j|) * |(1 : ℝ) / 8| ≤ 1 / 2 := by
    norm_num [Fin.sum_univ_three, firstBranchCoefficients]
  have h := taylorBranch firstBranchCoefficients firstBranchTerms (1 / 8) 2 u
    (basisFrame (zeroSignal 6)) firstBranchScale δ hTerms hStrength hPolynomial
  have hε : (2 : ℝ) / ((2 + 1 : Nat).factorial : ℝ) = 1 / 3 := by
    norm_num [Nat.factorial]
  rw [hε] at h
  exact h

/-- The Hermitian and dissipative matrices used by the four-grid fixture. -/
@[expose] noncomputable def sampleL : Matrix Bool Bool ℂ :=
  diagonal (fun bit => if bit then 1 / 2 else 3 / 2)

@[expose] noncomputable def sampleH : Matrix Bool Bool ℂ := ((1 : ℝ) / 4) • PauliX

theorem sampleL_posSemidef : sampleL.PosSemidef := by
  apply PosSemidef.diagonal
  intro b
  cases b <;> simp [Complex.nonneg_iff]
  norm_num

theorem sampleH_hermitian : sampleH.IsHermitian := by
  have hx : PauliX.IsHermitian := by
    show PauliXᴴ = PauliX
    exact permMatrix_conjTranspose Bool.not_not
  exact hx.smul (R := ℝ) (IsSelfAdjoint.all _)

theorem firstBranch_gridHamiltonian :
    firstBranchHamiltonian = sampleH + staticLchsGrid 1 4 (0 : Fin 4) • sampleL := by
  ext row col
  cases row <;> cases col <;>
    norm_num [firstBranchHamiltonian, firstBranchCoefficients, firstBranchTerms, Fin.sum_univ_three,
      sampleH, sampleL, staticLchsGrid, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      PauliX, PauliZ, permMatrix, Complex.real_smul]

/-- Apply the assembled theorem to the decoded nine-wire unitary after providing certificates
for its branches and the discrepancy of its physical success block. -/
theorem artifact_evolution {S : Type} [Fintype S] [DecidableEq S]
    (branches : Fin 4 → Matrix S S ℂ) (frame : Matrix S Bool ℂ) (α ε : Fin 4 → ℝ)
    (hBranches : ∀ j, BlockEncoding
      (hamiltonianEvolution (sampleH + staticLchsGrid 1 4 j • sampleL) (1 / 8))
      (branches j) frame frame (α j) (ε j))
    (u : WireMatrix 9) (hm : artifactTrace.matrix (fun _ => none) = .ok u) (δ : ℝ) :
    let c := staticLchsCoeff 1 4
    let a := ∑ j, ‖c j‖ * α j
    let f := basisFrame (zeroSignal 8)
    let g := tagFrame (0 : Fin 4) frame
    let ref := coefficientLCUUnitary (scaledLCUCoefficients c α) branches (0 : Fin 4)
    ‖a • (compress g ref g - compress f u f)‖ ≤ δ →
    BlockEncoding (staticNonunitaryEvolution sampleL sampleH (1 / 8)) u f f a
      ((∑ j, ‖c j‖ * ε j) + quadratureError sampleL (1 / 8) 1 4 + δ) := by
  dsimp only
  intro hδ
  obtain ⟨v, hv, hu⟩ := artifact_matrix
  rw [hm] at hv
  cases hv
  exact physicalBlock _ _ _ u _ _ _ δ
    (staticLCU sampleL sampleH (1 / 8) 1 4 0 branches frame α ε
      sampleL_posSemidef sampleH_hermitian (by norm_num) (by decide) hBranches)
    hu (basisFrame_isIsometry _) hδ

end OracqVerify.Verification.LCHS
