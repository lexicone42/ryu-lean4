/-
  IEEE754/Value.lean

  Mathematical interpretation of F64 values as rationals (ℚ).
  Uses Mathlib's rational numbers for exact arithmetic.

  Normal:    (-1)^s × (2^52 + m) × 2^(e - 1075)
  Subnormal: (-1)^s × m × 2^(-1074)
-/
import RyuLean4.IEEE754.Classify
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace F64

/-- The unbiased exponent for a normal number. -/
def unbiasedExp (x : F64) : Int :=
  (x.biasedExp.val : Int) - expBias

/-- The effective significand.
    Normal: 2^52 + mantissa.  Subnormal: mantissa. -/
def effectiveSignificand (x : F64) : Nat :=
  if x.biasedExp.val = 0 then x.mantissa.val
  else 2^mantBits + x.mantissa.val

/-- The effective binary exponent (accounting for implicit 2^52).
    Normal: biasedExp - 1075.  Subnormal: -1074. -/
def effectiveBinaryExp (x : F64) : Int :=
  if x.biasedExp.val = 0 then 1 - (expBias : Int) - mantBits
  else (x.biasedExp.val : Int) - expBias - mantBits

/-- The mathematical value of a finite F64 as a rational.
    value = (-1)^sign × significand × 2^binaryExp -/
def toRat (x : F64) : ℚ :=
  if ¬x.isFinite then 0
  else
    let sig : ℚ := x.effectiveSignificand
    let exp := x.effectiveBinaryExp
    let signMul : ℚ := if x.sign then -1 else 1
    if exp ≥ 0 then
      signMul * sig * (2 ^ exp.toNat : ℚ)
    else
      signMul * sig / (2 ^ (-exp).toNat : ℚ)

/-- Zero has rational value 0. -/
theorem toRat_posZero : posZero.toRat = 0 := by
  simp [toRat, posZero, isFinite, classify, effectiveSignificand,
        effectiveBinaryExp, expBias, mantBits]

/-- Negative zero also has rational value 0. -/
theorem toRat_negZero : negZero.toRat = 0 := by
  simp [toRat, negZero, isFinite, classify, effectiveSignificand,
        effectiveBinaryExp, expBias, mantBits]

end F64
