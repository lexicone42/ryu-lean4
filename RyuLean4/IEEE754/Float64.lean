/-
  IEEE754/Float64.lean

  IEEE 754 double-precision floating-point model.
  An F64 is decomposed into sign (1 bit), biased exponent (11 bits),
  and mantissa/significand (52 bits).

  Encoding (64 bits total):
    [63]     sign
    [62:52]  biased exponent (0..2047)
    [51:0]   mantissa

  Special values:
    exponent = 0,    mantissa = 0  → ±0
    exponent = 0,    mantissa ≠ 0  → subnormal
    exponent = 2047, mantissa = 0  → ±∞
    exponent = 2047, mantissa ≠ 0  → NaN
    otherwise                      → normal: (-1)^s × 2^(e-1023) × (1 + m/2^52)
-/

/-- IEEE 754 binary64 (double precision) floating-point number. -/
structure F64 where
  sign : Bool
  biasedExp : Fin 2048   -- 11-bit biased exponent (0..2047)
  mantissa : Fin (2^52)  -- 52-bit mantissa (0..2^52-1)
  deriving Repr, BEq, DecidableEq

namespace F64

-- IEEE 754 constants
def expBias : Nat := 1023
def expBits : Nat := 11
def mantBits : Nat := 52
def maxBiasedExp : Nat := 2047  -- 2^11 - 1

/-- Positive zero -/
def posZero : F64 := ⟨false, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Negative zero -/
def negZero : F64 := ⟨true, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Positive infinity -/
def posInf : F64 := ⟨false, ⟨2047, by omega⟩, ⟨0, by omega⟩⟩

/-- Negative infinity -/
def negInf : F64 := ⟨true, ⟨2047, by omega⟩, ⟨0, by omega⟩⟩

end F64
