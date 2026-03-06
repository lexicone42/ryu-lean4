/-
  IEEE754/RoundToNearest.lean

  Round-to-nearest-even: given a rational q, find the closest F64 value.
  On ties, pick the one with even mantissa LSB.
-/
import RyuLean4.IEEE754.Value
import Mathlib.Data.Rat.Floor

namespace F64

/-- Construct a finite F64, returning none on overflow. -/
def mkFinite (s : Bool) (bexp : Nat) (mant : Nat) : Option F64 :=
  if h1 : bexp < 2047 then
    if h2 : mant < 2^52 then
      some ⟨s, ⟨bexp, by omega⟩, ⟨mant, h2⟩⟩
    else none
  else none

/-- Find the biased exponent for a non-negative rational.
    Specification-level: iterate downward from 2046. -/
def findBiasedExp (qAbs : ℚ) : Nat :=
  let rec go (e : Nat) : Nat :=
    if e = 0 then 0
    else
      let threshold : ℚ :=
        if e ≥ 1023 then (2 ^ (e - 1023) : ℚ)
        else 1 / (2 ^ (1023 - e) : ℚ)
      if threshold ≤ qAbs then e
      else go (e - 1)
  termination_by e
  go 2046

/-- Round a non-negative rational to the nearest significand
    for a given biased exponent, with round-to-nearest-even.
    Returns (mantissa, bumpExponent). -/
def roundSignificand (qAbs : ℚ) (bexp : Nat) : Nat × Bool :=
  let binExp : Int :=
    if bexp = 0 then -1074
    else (bexp : Int) - 1075
  -- Scale q to the significand: sigExact = qAbs / 2^binExp
  let sigExact : ℚ :=
    if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
    else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  let sigRounded :=
    if remainder < 1/2 then sigFloor
    else if remainder > 1/2 then sigFloor + 1
    else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1
  let (mant, bumpExp) :=
    if bexp = 0 then
      if sigRounded ≥ 2^52 then (sigRounded - 2^52, true)
      else (sigRounded, false)
    else
      if sigRounded ≥ 2 * 2^52 then (sigRounded / 2 - 2^52, true)
      else if sigRounded < 2^52 then (sigRounded, false)
      else (sigRounded - 2^52, false)
  (mant, bumpExp)

/-- Round-to-nearest-even: map a rational to the closest F64 value. -/
def roundToNearestEven (q : ℚ) : F64 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    let (mant, bump) := roundSignificand qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

/-- The projection property for non-zero finite F64: rounding the value
    back gives the same F64. For zero, toRat maps both ±0 to 0 : ℚ,
    but roundToNearestEven(0) = posZero, so the roundtrip only works
    for posZero. The sign is preserved separately via the Decimal. -/
axiom round_nearest_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundToNearestEven (x.toRat) = x

end F64
