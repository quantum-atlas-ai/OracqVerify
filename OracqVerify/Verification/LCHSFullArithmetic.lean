module

public import OracqVerify.RIR.RationalUnitary
public import OracqVerify.Verification.LCHSFixture
meta import OracqVerify.RIR.RationalUnitary
meta import OracqVerify.Verification.LCHSFixture

/-! Exact rational checks for both columns of the four-node LCHS artifact. -/

set_option warningAsError true
set_option maxRecDepth 8000

public section

namespace OracqVerify.Verification.LCHS

open RIR Qatlib.Foundations.PureStateMath

attribute [local semireducible] Rat.mul Rat.inv Rat.add Rat.sub

@[expose] def artifactActions : List (GateAction 9) :=
  (artifactTrace.instructions.mapM (GateAction.lower 9 false)).toOption.getD []

@[expose] def artifactRationalColumn (col : Bool) : Reg 9 → Gaussian :=
  GateAction.runRational artifactActions (rationalKet (zeroSignal 8 col))

@[expose] def taylorNumerator (row col : Bool) : Gaussian :=
  if row = col then
    if row then ⟨63421 / 40960, 1 / 64⟩ else ⟨63133 / 40960, 3 / 64⟩
  else ⟨1 / 1024, -(31 / 640)⟩

@[expose] def artifactRationalScale : ℚ := 551563578415394 / 10^15
@[expose] def rationalPiLower : ℚ := 314159265358979323846 / 10^20

@[expose] def artifactEntryDiscrepancy (row col : Bool) (entry : Gaussian) : Gaussian :=
  taylorNumerator row col - (⟨rationalPiLower * artifactRationalScale, 0⟩ : Gaussian) * entry

private def checkColumn (col : Bool) : Bool :=
  let values := artifactRationalColumn col
  [false, true].all fun row =>
    let value := artifactEntryDiscrepancy row col (values (zeroSignal 8 row))
    decide (|value.re| + |value.im| ≤ (1 : ℚ) / 10^12)

-- These two closed arithmetic comparisons use Lean's compiled evaluator.
private theorem column_zero : checkColumn false = true := by native_decide

private theorem column_one : checkColumn true = true := by native_decide

theorem checked_columns (row col : Bool) :
    let d := artifactEntryDiscrepancy row col (artifactRationalColumn col (zeroSignal 8 row))
    |d.re| + |d.im| ≤ (1 : ℚ) / 10^12 := by
  have checked : checkColumn col = true := by cases col; exact column_zero; exact column_one
  have h := List.all_eq_true.mp checked row (by cases row <;> simp)
  exact of_decide_eq_true h

end OracqVerify.Verification.LCHS
