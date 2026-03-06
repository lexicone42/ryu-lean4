/-
  Ryu/Interval.lean

  The acceptance interval: for a finite F64 x, the set of rationals
  that round to x under round-to-nearest-even.
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Data.Rat.Defs

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
    Uses min/max to ensure low ≤ high for both positive and negative floats. -/
def schubfachInterval (x : F64) (_hfin : x.isFinite) : AcceptanceInterval :=
  let xVal := x.toRat
  let xPrev := f64Pred x
  let xNext := f64Succ x
  let bound1 := (xPrev.toRat + xVal) / 2
  let bound2 := (xVal + xNext.toRat) / 2
  let mantEven := x.mantissa.val % 2 = 0
  { low := min bound1 bound2
    high := max bound1 bound2
    lowInclusive := mantEven
    highInclusive := mantEven }

/-- The acceptance interval is sound: any rational in the interval
    rounds to x. Axiomatized for now. -/
axiom schubfach_interval_correct (x : F64) (hfin : x.isFinite)
    (q : ℚ) (hq : (schubfachInterval x hfin).contains q) :
    F64.roundToNearestEven q = x

end Ryu
