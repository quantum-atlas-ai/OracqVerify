module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Field.Rat

/-! Rational outward enclosures for the operations of the real Roe reference. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.RationalEnclosure

structure Range where
  lo : ℚ
  hi : ℚ

def Range.Covers (bounds : Range) (value : ℝ) : Prop :=
  (bounds.lo : ℝ) ≤ value ∧ value ≤ (bounds.hi : ℝ)

def Range.point (x : ℚ) : Range := ⟨x, x⟩

theorem Range.point_covers (x : ℚ) : (point x).Covers (x : ℝ) := ⟨le_rfl, le_rfl⟩

def Range.add (x y : Range) : Range := ⟨x.lo + y.lo, x.hi + y.hi⟩

theorem Range.add_covers {x y : Range} {a b : ℝ} (ha : x.Covers a) (hb : y.Covers b) :
    (x.add y).Covers (a + b) := by
  exact ⟨by simpa [add] using add_le_add ha.1 hb.1, by simpa [add] using add_le_add ha.2 hb.2⟩

def Range.neg (x : Range) : Range := ⟨-x.hi, -x.lo⟩

theorem Range.neg_covers {x : Range} {a : ℝ} (ha : x.Covers a) :
    x.neg.Covers (-a) := by
  exact ⟨by simpa [neg] using neg_le_neg ha.2, by simpa [neg] using neg_le_neg ha.1⟩

def Range.mul (x y : Range) : Range :=
  ⟨min (min (x.lo * y.lo) (x.hi * y.lo)) (min (x.lo * y.hi) (x.hi * y.hi)),
   max (max (x.lo * y.lo) (x.hi * y.lo)) (max (x.lo * y.hi) (x.hi * y.hi))⟩

private theorem between_multiples {lo hi value factor : ℝ} (hl : lo ≤ value) (hh : value ≤ hi) :
    min (lo * factor) (hi * factor) ≤ value * factor ∧ value * factor ≤ max (lo * factor) (hi * factor) := by
  by_cases nonneg : 0 ≤ factor
  · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_right hl nonneg),
      (mul_le_mul_of_nonneg_right hh nonneg).trans (le_max_right ..)⟩
  · have nonpos : factor ≤ 0 := le_of_lt (lt_of_not_ge nonneg)
    exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_right hh nonpos),
      (mul_le_mul_of_nonpos_right hl nonpos).trans (le_max_left ..)⟩

theorem Range.mul_covers {x y : Range} {a b : ℝ} (ha : x.Covers a) (hb : y.Covers b) :
    (x.mul y).Covers (a * b) := by
  have lo := between_multiples (factor := (y.lo : ℝ)) ha.1 ha.2
  have hi := between_multiples (factor := (y.hi : ℝ)) ha.1 ha.2
  unfold Covers mul
  push_cast
  by_cases nonneg : 0 ≤ a
  · exact ⟨(min_le_left ..).trans (lo.1.trans (mul_le_mul_of_nonneg_left hb.1 nonneg)),
      (mul_le_mul_of_nonneg_left hb.2 nonneg).trans (hi.2.trans (le_max_right ..))⟩
  · have nonpos : a ≤ 0 := le_of_lt (lt_of_not_ge nonneg)
    exact ⟨(min_le_right ..).trans (hi.1.trans (mul_le_mul_of_nonpos_left hb.2 nonpos)),
      (mul_le_mul_of_nonpos_left hb.1 nonpos).trans (lo.2.trans (le_max_left ..))⟩

def Range.inv (x : Range) : Range := ⟨x.hi⁻¹, x.lo⁻¹⟩

theorem Range.inv_covers {x : Range} {a : ℝ} (positive : 0 < x.lo) (ha : x.Covers a) :
    x.inv.Covers a⁻¹ := by
  have lo : 0 < (x.lo : ℝ) := by exact_mod_cast positive
  have apos : 0 < a := lo.trans_le ha.1
  have lower := (inv_le_inv₀ (apos.trans_le ha.2) apos).mpr ha.2
  have upper := (inv_le_inv₀ apos lo).mpr ha.1
  exact ⟨by simpa [inv] using lower, by simpa [inv] using upper⟩

theorem Range.sqrt_covers {x root : Range} {a : ℝ} (ha : x.Covers a)
    (nonneg : 0 ≤ root.hi) (lo : root.lo ^ 2 ≤ x.lo) (hi : x.hi ≤ root.hi ^ 2) :
    root.Covers (Real.sqrt a) := by
  have realLo : ((root.lo : ℚ) : ℝ)^2 ≤ (x.lo : ℝ) := by exact_mod_cast lo
  have realHi : (x.hi : ℝ) ≤ ((root.hi : ℚ) : ℝ)^2 := by exact_mod_cast hi
  have realNonneg : 0 ≤ (root.hi : ℝ) := by exact_mod_cast nonneg
  exact ⟨Real.le_sqrt_of_sq_le (realLo.trans ha.1), Real.sqrt_le_iff.mpr ⟨realNonneg, ha.2.trans realHi⟩⟩


def sqrtGrid : ℕ := 2 ^ 48

def Range.gridRoot (x : ℚ) : ℕ :=
  let scaled := x * sqrtGrid ^ 2
  Nat.sqrt (scaled.num.toNat / scaled.den)

def Range.root (bounds : Range) : Range :=
  ⟨(gridRoot bounds.lo : ℚ) / sqrtGrid, ((gridRoot bounds.hi + 1 : ℕ) : ℚ) / sqrtGrid⟩

inductive Expr where
  | rational (number : ℚ)
  | add (left right : Expr)
  | mul (left right : Expr)
  | neg (arg : Expr)
  | inv (arg : Expr)
  | sqrt (arg : Expr)
  | chooseLE (left right onTrue onFalse : Expr)

noncomputable def Expr.denote : Expr → ℝ
  | .rational q => q
  | .add a b => a.denote + b.denote
  | .mul a b => a.denote * b.denote
  | .neg a => -a.denote
  | .inv a => a.denote⁻¹
  | .sqrt a => Real.sqrt a.denote
  | .chooseLE a b onTrue onFalse =>
    if a.denote ≤ b.denote then onTrue.denote else onFalse.denote

/-- Every successful step carries a proof that its dyadic or rational enclosure
contains the denotation. A square-root candidate is checked by squaring its endpoints. -/
def Expr.certify : (expr : Expr) → Option {bounds : Range // bounds.Covers expr.denote}
  | .rational q => some ⟨Range.point q, Range.point_covers q⟩
  | .add a b => do
    let ⟨left, leftOk⟩ ← a.certify
    let ⟨right, rightOk⟩ ← b.certify
    return ⟨left.add right, Range.add_covers leftOk rightOk⟩
  | .mul a b => do
    let ⟨left, leftOk⟩ ← a.certify
    let ⟨right, rightOk⟩ ← b.certify
    return ⟨left.mul right, Range.mul_covers leftOk rightOk⟩
  | .neg a => do
    let ⟨bounds, ok⟩ ← a.certify
    return ⟨bounds.neg, Range.neg_covers ok⟩
  | .inv a => do
    let ⟨bounds, ok⟩ ← a.certify
    if positive : 0 < bounds.lo then
      some ⟨bounds.inv, Range.inv_covers positive ok⟩
    else none
  | .sqrt a => do
    let ⟨bounds, ok⟩ ← a.certify
    let guess := bounds.root
    if valid : 0 ≤ guess.hi ∧ guess.lo ^ 2 ≤ bounds.lo ∧ bounds.hi ≤ guess.hi ^ 2 then
      some ⟨guess, Range.sqrt_covers ok valid.1 valid.2.1 valid.2.2⟩
    else none
  | .chooseLE a b onTrue onFalse => do
    let ⟨left, leftOk⟩ ← a.certify
    let ⟨right, rightOk⟩ ← b.certify
    if ordered : left.hi ≤ right.lo then
      let ⟨bounds, ok⟩ ← onTrue.certify
      have realOrdered : (left.hi : ℝ) ≤ (right.lo : ℝ) := by exact_mod_cast ordered
      have selected := leftOk.2.trans (realOrdered.trans rightOk.1)
      return ⟨bounds, by simpa [Expr.denote, selected] using ok⟩
    else if reversed : right.hi < left.lo then
      let ⟨bounds, ok⟩ ← onFalse.certify
      have realReversed : (right.hi : ℝ) < (left.lo : ℝ) := by exact_mod_cast reversed
      have rejected := not_le_of_gt (rightOk.2.trans_lt (realReversed.trans_le leftOk.1))
      return ⟨bounds, by simpa [Expr.denote, rejected] using ok⟩
    else none


namespace Expr

instance (n : Nat) : OfNat Expr n := ⟨.rational (n : ℚ)⟩
instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Neg Expr := ⟨.neg⟩
instance : Sub Expr := ⟨fun a b => a + (-b)⟩
instance : Div Expr := ⟨fun a b => a * .inv b⟩

def abs (x : Expr) : Expr := .chooseLE 0 x x (-x)

end Expr

def Expr.absUpper (expr : Expr) : Option ℚ :=
  expr.certify.map fun certified => max (-certified.val.lo) certified.val.hi

theorem Expr.absUpper_sound {expr : Expr} {bound : ℚ} (verified : expr.absUpper = some bound) :
    |expr.denote| ≤ (bound : ℝ) := by
  unfold absUpper at verified
  cases enclosed : expr.certify with
  | none => rw [enclosed] at verified; cases verified
  | some evidence =>
    rw [enclosed] at verified
    cases verified
    refine abs_le.mpr ⟨?_, ?_⟩
    · have lower : (-evidence.val.lo : ℚ) ≤ max (-evidence.val.lo) evidence.val.hi :=
        le_max_left _ _
      have cast : -(evidence.val.lo : ℝ) ≤ ((max (-evidence.val.lo) evidence.val.hi : ℚ) : ℝ) := by
        exact_mod_cast lower
      exact (by simpa using neg_le_neg cast : -((max (-evidence.val.lo) evidence.val.hi : ℚ) : ℝ) ≤
        (evidence.val.lo : ℝ)).trans evidence.property.1
    · have upper : ((evidence.val.hi : ℚ) : ℝ) ≤ ((max (-evidence.val.lo) evidence.val.hi : ℚ) : ℝ) := by
        exact_mod_cast (le_max_right (-evidence.val.lo) evidence.val.hi)
      exact evidence.property.2.trans upper


end OracqVerify.Verification.RationalEnclosure
