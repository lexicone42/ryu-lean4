/-
  IEEE754/Classify.lean

  Classification of F64 values into zero, subnormal, normal, infinity, NaN.
-/
import RyuLean4.IEEE754.Float64

/-- The class of an IEEE 754 float. -/
inductive FloatClass where
  | zero
  | subnormal
  | normal
  | infinity
  | nan
  deriving Repr, BEq, DecidableEq

namespace F64

/-- Classify an F64 value. -/
def classify (x : F64) : FloatClass :=
  if x.biasedExp.val = 0 then
    if x.mantissa.val = 0 then .zero
    else .subnormal
  else if x.biasedExp.val = 2047 then
    if x.mantissa.val = 0 then .infinity
    else .nan
  else .normal

/-- An F64 is finite if it is zero, subnormal, or normal. -/
def isFinite (x : F64) : Prop :=
  x.classify = .zero ∨ x.classify = .subnormal ∨ x.classify = .normal

instance : Decidable (isFinite x) := by
  unfold isFinite
  exact inferInstance

/-- An F64 is zero. -/
def isZero (x : F64) : Prop := x.classify = .zero

/-- An F64 is subnormal. -/
def isSubnormal (x : F64) : Prop := x.classify = .subnormal

/-- An F64 is normal. -/
def isNormal (x : F64) : Prop := x.classify = .normal

/-- Finite F64 values have biased exponent < 2047. -/
theorem finite_implies_exp_lt (x : F64) (hfin : x.isFinite) :
    x.biasedExp.val < 2047 := by
  unfold isFinite classify at hfin
  have hbound := x.biasedExp.isLt
  rcases hfin with h | h | h <;> {
    split at h
    · split at h <;> simp at h <;> omega
    · split at h
      · split at h <;> simp at h
      · simp at h <;> omega
  }

theorem exp_lt_implies_finite (x : F64) (h : x.biasedExp.val < 2047) :
    x.isFinite := by
  unfold isFinite classify
  by_cases he : x.biasedExp.val = 0
  · by_cases hm : x.mantissa.val = 0
    · left; simp [he, hm]
    · right; left; simp [he, hm]
  · right; right; simp [he]; omega

end F64
