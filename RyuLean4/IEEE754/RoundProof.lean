/-
  IEEE754/RoundProof.lean

  Proof of the projection property:
    roundToNearestEven(toRat(x)) = x  for all finite non-zero x
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace F64

/-! ## Helper lemmas -/

/-- For a finite F64, effectiveSignificand is bounded. -/
theorem effectiveSignificand_lt (x : F64) (_hfin : x.isFinite) :
    x.effectiveSignificand < 2^53 := by
  unfold effectiveSignificand
  split
  · exact Nat.lt_trans x.mantissa.isLt (by omega)
  · have := x.mantissa.isLt
    show 2 ^ mantBits + x.mantissa.val < 2 ^ 53
    simp [mantBits]; omega

/-- For zero, toRat is 0 and roundToNearestEven(0) = posZero. -/
theorem round_zero : roundToNearestEven 0 = posZero := by
  simp [roundToNearestEven]

theorem round_idempotent_posZero : roundToNearestEven posZero.toRat = posZero := by
  rw [toRat_posZero]; exact round_zero

theorem round_idempotent_negZero : roundToNearestEven negZero.toRat = posZero := by
  rw [toRat_negZero]; exact round_zero

/-! ## Sign properties -/

private theorem effectiveSig_ne_zero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    x.effectiveSignificand ≠ 0 := by
  intro h; apply hne
  unfold toRat; rw [if_neg (not_not.mpr hfin)]; simp [h]

/-- The sign of toRat agrees with x.sign for finite non-zero x. -/
theorem toRat_lt_zero_iff (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    x.toRat < 0 ↔ x.sign = true := by
  have hsig_pos : (0 : ℚ) < x.effectiveSignificand :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (effectiveSig_ne_zero x hfin hne))
  constructor
  · intro h
    cases hs : x.sign
    · exfalso
      unfold toRat at h; rw [if_neg (not_not.mpr hfin)] at h
      simp only [] at h; rw [hs] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · linarith [mul_nonneg (le_of_lt hsig_pos)
          (show (0 : ℚ) ≤ 2 ^ x.effectiveBinaryExp.toNat by positivity)]
      · linarith [div_nonneg (mul_nonneg (le_refl (1 : ℚ)) (le_of_lt hsig_pos))
          (show (0 : ℚ) ≤ 2 ^ (-x.effectiveBinaryExp).toNat by positivity)]
    · rfl
  · intro hs
    unfold toRat; rw [if_neg (not_not.mpr hfin)]
    simp only []; rw [hs]; simp only [↓reduceIte]
    split
    · nlinarith [mul_pos hsig_pos (show (0 : ℚ) < 2 ^ x.effectiveBinaryExp.toNat by positivity)]
    · apply div_neg_of_neg_of_pos <;> [nlinarith; positivity]

/-! ## mkFinite success -/

theorem mkFinite_eq (s : Bool) (e : Fin 2048) (m : Fin (2^52))
    (he : e.val < 2047) :
    mkFinite s e.val m.val = some ⟨s, ⟨e.val, by omega⟩, ⟨m.val, m.isLt⟩⟩ := by
  unfold mkFinite
  simp only [show e.val < 2047 from he, show m.val < 2 ^ 52 from m.isLt,
             dite_true]

/-! ## findBiasedExp correctness -/

/-- findBiasedExp correctly recovers the biased exponent. -/
theorem findBiasedExp_correct (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    findBiasedExp |x.toRat| = x.biasedExp.val := by
  sorry

/-! ## roundSignificand exactness -/

/-- roundSignificand recovers the mantissa exactly with no bump. -/
theorem roundSignificand_exact (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundSignificand |x.toRat| x.biasedExp.val = (x.mantissa.val, false) := by
  sorry

/-! ## Main composition -/

/-- roundToNearestEven(x.toRat) = x for finite non-zero x.
    Proof: unfold roundToNearestEven, show findBiasedExp and roundSignificand
    recover the original biased exponent and mantissa, then mkFinite reconstructs x. -/
theorem round_nearest_nonzero' (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundToNearestEven (x.toRat) = x := by
  unfold roundToNearestEven
  rw [if_neg hne]
  simp only []
  have hfbe := findBiasedExp_correct x hfin hne
  have hrs := roundSignificand_exact x hfin hne
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  rw [hfbe, hrs]
  simp only []
  -- Split on bump condition (false = true): trivially false
  split
  · next h => exact absurd h (by decide)
  · -- Split on finalExp ≥ maxBiasedExp: contradiction with hexp_lt
    split
    · next h => exfalso; unfold maxBiasedExp at h; omega
    · -- Match on mkFinite result
      split
      · -- mkFinite = some val
        next hmk =>
        have hdec : decide (x.toRat < 0) = x.sign := by
          cases hs : x.sign
          · exact decide_eq_false (mt hsign.mp (by simp [hs]))
          · exact decide_eq_true (hsign.mpr hs)
        unfold mkFinite at hmk
        simp only [show x.biasedExp.val < 2047 from hexp_lt,
                   show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true] at hmk
        rw [hdec] at hmk
        simp only [Option.some.injEq] at hmk
        rw [← hmk]
      · -- mkFinite = none: contradiction
        next hmk =>
        exfalso; unfold mkFinite at hmk
        simp [show x.biasedExp.val < 2047 from hexp_lt] at hmk

end F64
