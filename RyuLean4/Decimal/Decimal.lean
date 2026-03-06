/-
  Decimal/Decimal.lean

  Decimal floating-point representation.
  A Decimal number is: (-1)^sign × digits × 10^exponent
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Data.Rat.Defs

/-- A decimal floating-point number. -/
structure Decimal where
  sign : Bool
  digits : Nat
  exponent : Int
  deriving Repr, BEq, DecidableEq

namespace Decimal

def zero : Decimal := ⟨false, 0, 0⟩

/-- Count decimal digits in a natural number. -/
private def countDigits (n : Nat) : Nat :=
  if n < 10 then 1
  else 1 + countDigits (n / 10)
termination_by n

/-- The number of significant decimal digits. -/
def numDigits (d : Decimal) : Nat :=
  countDigits d.digits

/-- Convert a Decimal to a rational. -/
def toRat (d : Decimal) : ℚ :=
  let signMul : ℚ := if d.sign then -1 else 1
  if d.exponent ≥ 0 then
    signMul * d.digits * (10 ^ d.exponent.toNat : ℚ)
  else
    signMul * d.digits / (10 ^ (-d.exponent).toNat : ℚ)

/-- Convert a Decimal to F64 via rounding. -/
def toF64 (d : Decimal) : F64 :=
  F64.roundToNearestEven d.toRat

/-- A Decimal is well-formed if:
    1. Non-zero digits have no trailing zeros (digits % 10 ≠ 0)
    2. sign is false when digits = 0 -/
def WellFormed (d : Decimal) : Prop :=
  (d.digits ≠ 0 → d.digits % 10 ≠ 0) ∧
  (d.digits = 0 → d.sign = false)

end Decimal
