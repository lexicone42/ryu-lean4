/-
  Ryu/Interval.lean

  The acceptance interval: for a finite F64 x, the set of rationals
  that round to x under round-to-nearest-even.
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Ryu

/-- An interval with boundary inclusivity flags. -/
structure AcceptanceInterval where
  low : ℚ
  high : ℚ
  lowInclusive : Bool
  highInclusive : Bool
  deriving Repr

/-- Membership in an acceptance interval. -/
def AcceptanceInterval.contains (iv : AcceptanceInterval) (q : ℚ) : Prop :=
  (if iv.lowInclusive then iv.low ≤ q else iv.low < q) ∧
  (if iv.highInclusive then q ≤ iv.high else q < iv.high)

/-- Predecessor of an F64 value. -/
def f64Pred (x : F64) : F64 :=
  if x.mantissa.val > 0 then
    ⟨x.sign, x.biasedExp, ⟨x.mantissa.val - 1, by omega⟩⟩
  else if h : x.biasedExp.val > 0 then
    ⟨x.sign, ⟨x.biasedExp.val - 1, by omega⟩, ⟨2^52 - 1, by omega⟩⟩
  else
    ⟨!x.sign, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Successor of an F64 value. -/
def f64Succ (x : F64) : F64 :=
  if h : x.mantissa.val + 1 < 2^52 then
    ⟨x.sign, x.biasedExp, ⟨x.mantissa.val + 1, h⟩⟩
  else if h2 : x.biasedExp.val + 1 < 2048 then
    ⟨x.sign, ⟨x.biasedExp.val + 1, h2⟩, ⟨0, by omega⟩⟩
  else
    ⟨x.sign, ⟨2047, by omega⟩, ⟨0, by omega⟩⟩

/-- Compute the acceptance interval for a finite F64 value.
    Based on the algebraic (u, v, w) · 2^e₂ representation from the Ryu paper (Section 2.2).
    u = 4·mf - δ, w = 4·mf + 2, e₂ = ef - 2
    δ = 1 if mantissa=0 and biasedExp>1 (exponent boundary), else δ = 2. -/
def schubfachInterval (x : F64) (_hfin : x.isFinite) : AcceptanceInterval :=
  let mf := x.effectiveSignificand
  let e2 := x.effectiveBinaryExp - 2
  let delta : Nat := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2
  let u : Nat := 4 * mf - delta
  let w : Nat := 4 * mf + 2
  let mantEven := x.mantissa.val % 2 = 0
  let scaleN (n : Nat) : ℚ :=
    if e2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ e2.toNat
    else (n : ℚ) / (2 : ℚ) ^ (-e2).toNat
  if x.sign then
    { low := -(scaleN w), high := -(scaleN u),
      lowInclusive := mantEven, highInclusive := mantEven }
  else
    { low := scaleN u, high := scaleN w,
      lowInclusive := mantEven, highInclusive := mantEven }

/-- The acceptance interval is sound: any rational in the interval
    rounds to x. Axiomatized for now. -/
axiom schubfach_interval_correct (x : F64) (hfin : x.isFinite)
    (q : ℚ) (hq : (schubfachInterval x hfin).contains q) :
    F64.roundToNearestEven q = x

private theorem effSig_pos_of_toRat_ne_zero (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) : x.effectiveSignificand ≥ 1 := by
  by_contra h; push_neg at h
  have : x.effectiveSignificand = 0 := by omega
  exact hne (by unfold F64.toRat; rw [if_neg (not_not.mpr hfin)]; simp [this])

private theorem scaleN_pos_and_lt {u w : Nat} (hu : 0 < u) (hw : u < w) (e2 : Int) :
    0 < (if e2 ≥ 0 then (u : ℚ) * (2 : ℚ) ^ e2.toNat
         else (u : ℚ) / (2 : ℚ) ^ (-e2).toNat) ∧
    (if e2 ≥ 0 then (u : ℚ) * (2 : ℚ) ^ e2.toNat
     else (u : ℚ) / (2 : ℚ) ^ (-e2).toNat) <
    (if e2 ≥ 0 then (w : ℚ) * (2 : ℚ) ^ e2.toNat
     else (w : ℚ) / (2 : ℚ) ^ (-e2).toNat) := by
  by_cases he : e2 ≥ 0
  · simp only [if_pos he]
    exact ⟨mul_pos (by exact_mod_cast hu) (by positivity),
           mul_lt_mul_of_pos_right (by exact_mod_cast hw) (by positivity)⟩
  · simp only [if_neg he]
    exact ⟨div_pos (by exact_mod_cast hu) (by positivity),
           div_lt_div_of_pos_right (by exact_mod_cast hw) (by positivity)⟩

/-- The absolute interval (negated/swapped for negative floats) has
    strictly positive bounds with low < high.
    Proof: from the algebraic (u,w) representation, u ≥ 2 > 0 and w > u
    for any non-zero finite float. -/
theorem schubfach_abs_interval_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    let iv := schubfachInterval x hfin
    let absIv := if x.sign then
      { low := -iv.high, high := -iv.low,
        lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive : AcceptanceInterval }
    else iv
    0 < absIv.low ∧ absIv.low < absIv.high := by
  simp only []
  have hmf := effSig_pos_of_toRat_ne_zero x hfin hne
  have hu_pos : 0 < 4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) := by
    split <;> omega
  have hw_gt : 4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) <
      4 * x.effectiveSignificand + 2 := by
    split <;> omega
  have key := scaleN_pos_and_lt hu_pos hw_gt (x.effectiveBinaryExp - 2)
  cases hs : x.sign
  · -- sign = false: absIv = iv, if-else reduces to pos branch
    unfold schubfachInterval
    simp only [hs]
    exact key
  · -- sign = true: absIv negates, double negation cancels
    unfold schubfachInterval
    simp only [hs, ↓reduceIte, neg_neg]
    exact key

end Ryu
