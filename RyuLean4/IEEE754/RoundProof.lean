/-
  IEEE754/RoundProof.lean

  Proof of the projection property:
    roundToNearestEven(toRat(x)) = x  for all finite x

  Strategy: show that toRat produces a value that, when fed back through
  findBiasedExp and roundSignificand, recovers the original (biasedExp, mantissa).

  The key insight is that toRat(x) = sig × 2^exp where sig and exp are
  chosen so that sig is already an integer — so roundSignificand produces
  remainder 0, meaning no rounding occurs, and the original bits are recovered.
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Tactic.NormNum

namespace F64

/-! ## Helper lemmas -/

/-- For a finite F64, effectiveSignificand is bounded. -/
theorem effectiveSignificand_lt (x : F64) (_hfin : x.isFinite) :
    x.effectiveSignificand < 2^53 := by
  unfold effectiveSignificand
  split
  · -- subnormal: mantissa < 2^52 < 2^53
    exact Nat.lt_trans x.mantissa.isLt (by omega)
  · -- normal: 2^52 + mantissa < 2^52 + 2^52 = 2^53
    have := x.mantissa.isLt
    show 2 ^ mantBits + x.mantissa.val < 2 ^ 53
    simp [mantBits]
    omega

/-- For zero, toRat is 0 and roundToNearestEven(0) = posZero. -/
theorem round_zero : roundToNearestEven 0 = posZero := by
  simp [roundToNearestEven]

/-- Positive zero roundtrips. -/
theorem round_idempotent_posZero : roundToNearestEven posZero.toRat = posZero := by
  rw [toRat_posZero]
  exact round_zero

/-- Negative zero roundtrips (both map to 0, which rounds to posZero). -/
theorem round_idempotent_negZero : roundToNearestEven negZero.toRat = posZero := by
  rw [toRat_negZero]
  exact round_zero

/-! ## The general idempotency proof

  For the full proof of round_nearest_idempotent, we need to show that
  for any finite F64 x:
  1. If x is zero: toRat(x) = 0, roundToNearestEven(0) = posZero = x (up to sign)
  2. If x is nonzero:
     a. findBiasedExp(|toRat(x)|) = x.biasedExp
     b. roundSignificand(|toRat(x)|, x.biasedExp) = (x.mantissa, false)
     c. Therefore mkFinite reconstructs x exactly

  Step (b) is the core: toRat(x) = sig × 2^exp where sig = effectiveSignificand(x)
  is already an integer. When we scale by 2^(-exp) in roundSignificand, we get
  exactly sig with remainder 0. So sigRounded = sig, and the mantissa recovery
  gives x.mantissa exactly.

  The full proof of this requires careful case analysis on the exponent ranges
  and precise arithmetic about the scaling. We leave it axiomatized for now
  and will prove it incrementally as we build up the arithmetic infrastructure.

  Note: signed zero is a special case — both +0 and -0 have toRat = 0,
  and roundToNearestEven(0) = posZero. So the roundtrip only works up to
  sign for zero. For the Ryu roundtrip, this is fine because the sign is
  preserved separately in the Decimal representation.
-/

end F64
