/-
  IEEE754/RoundProof.lean

  Proof of the projection property:
    roundToNearestEven(toRat(x)) = x  for all finite non-zero x
-/
import RyuLean4.IEEE754.RoundToNearest
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

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

/-! ## |toRat| characterization -/

theorem toRat_abs (x : F64) (hfin : x.isFinite) :
    |x.toRat| =
      if x.effectiveBinaryExp ≥ 0 then
        (x.effectiveSignificand : ℚ) * 2 ^ x.effectiveBinaryExp.toNat
      else
        (x.effectiveSignificand : ℚ) / 2 ^ (-x.effectiveBinaryExp).toNat := by
  unfold toRat; rw [if_neg (not_not.mpr hfin)]; simp only []
  have hsig_nn : (0 : ℚ) ≤ x.effectiveSignificand := Nat.cast_nonneg _
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    have h2 : (0 : ℚ) ≤ 2 ^ x.effectiveBinaryExp.toNat := by positivity
    cases x.sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [abs_of_nonneg (by nlinarith [mul_nonneg hsig_nn h2])]; ring
    · rw [abs_of_nonpos (by nlinarith [mul_nonneg hsig_nn h2])]; ring
  · simp only [if_neg hexp]
    have h2 : (0 : ℚ) < 2 ^ (-x.effectiveBinaryExp).toNat := by positivity
    cases x.sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [abs_of_nonneg (div_nonneg (by nlinarith) (le_of_lt h2))]; ring
    · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt h2))]; ring

/-! ## findBiasedExp correctness -/

private def threshQ (e : Nat) : ℚ :=
  if e ≥ 1023 then (2 ^ (e - 1023) : ℚ) else 1 / (2 ^ (1023 - e) : ℚ)

private theorem threshQ_le_of_le {a b : Nat} (h : a ≤ b) : threshQ a ≤ threshQ b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · unfold threshQ
    by_cases ha : a ≥ 1023 <;> by_cases hb : b ≥ 1023
    · simp only [show a ≥ 1023 from ha, show b ≥ 1023 from hb, ↓reduceIte]
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    · omega
    · push_neg at ha
      simp only [show ¬(a ≥ 1023) from by omega, show b ≥ 1023 from hb, ↓reduceIte]
      calc 1 / (2 : ℚ) ^ (1023 - a)
          ≤ 1 := by rw [one_div]; exact inv_le_one_of_one_le₀
                      (by exact_mod_cast Nat.one_le_pow _ _ (by omega))
        _ ≤ (2 : ℚ) ^ (b - 1023) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    · push_neg at ha hb
      simp only [show ¬(a ≥ 1023) from by omega, show ¬(b ≥ 1023) from by omega, ↓reduceIte]
      rw [one_div, one_div]
      exact inv_anti₀ (by positivity)
        (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))

private theorem go_eq (qAbs : ℚ) (target : Nat) :
    ∀ start, target ≤ start →
      (target = 0 ∨ threshQ target ≤ qAbs) →
      (∀ e, target < e → e ≤ start → ¬(threshQ e ≤ qAbs)) →
      findBiasedExp.go qAbs start = target := by
  intro start
  induction start using Nat.strongRecOn with
  | _ start ih =>
    intro h_le h_target h_above
    unfold findBiasedExp.go
    by_cases hstart : start = 0
    · simp [hstart]; omega
    · rw [if_neg hstart]; simp only []
      show (if threshQ start ≤ qAbs then start
            else findBiasedExp.go qAbs (start - 1)) = target
      by_cases hthresh : threshQ start ≤ qAbs
      · rw [if_pos hthresh]
        by_contra hne; exact h_above start (by omega) le_rfl hthresh
      · rw [if_neg hthresh]
        have hlt_start : target < start := by
          rcases h_target with rfl | htq
          · omega
          · by_contra hge; push_neg at hge
            exact hthresh (by rwa [show target = start from by omega] at htq)
        exact ih (start - 1) (by omega) (by omega) h_target
          (fun e he hle => h_above e he (by omega))

private theorem ebe_normal (x : F64) (h : x.biasedExp.val ≠ 0) :
    x.effectiveBinaryExp = (x.biasedExp.val : Int) - 1075 := by
  unfold effectiveBinaryExp expBias mantBits; split <;> omega

private theorem esig_ge_52 (x : F64) (h : x.biasedExp.val ≥ 1) :
    (x.effectiveSignificand : ℚ) ≥ 2^52 := by
  have : x.effectiveSignificand ≥ 2^52 := by
    unfold effectiveSignificand; simp only [mantBits]; split <;> omega
  exact_mod_cast this

private theorem esig_lt_53 (x : F64) :
    (x.effectiveSignificand : ℚ) < 2^53 := by
  suffices h : x.effectiveSignificand < 2^53 from by exact_mod_cast h
  unfold effectiveSignificand; simp only [mantBits]
  have hm := x.mantissa.isLt
  split
  · linarith [show (2:Nat)^52 < 2^53 from by norm_num]
  · linarith [show (2:Nat)^52 + 2^52 = 2^53 from by norm_num]

private theorem esig_lt_52_sub (x : F64) (h : x.biasedExp.val = 0) :
    (x.effectiveSignificand : ℚ) < 2^52 := by
  suffices hh : x.effectiveSignificand < 2^52 by exact_mod_cast hh
  unfold effectiveSignificand; simp [h]

private theorem lower_bound (x : F64) (hfin : x.isFinite) (hbexp : x.biasedExp.val ≥ 1) :
    threshQ x.biasedExp.val ≤ |x.toRat| := by
  rw [toRat_abs x hfin]
  have hesig := esig_ge_52 x hbexp
  have hbne : x.biasedExp.val ≠ 0 := by omega
  have hebe := ebe_normal x hbne
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    have hbge : x.biasedExp.val ≥ 1075 := by rw [hebe] at hexp; omega
    have htonat : x.effectiveBinaryExp.toNat = x.biasedExp.val - 1075 := by
      rw [hebe]; omega
    rw [htonat]
    unfold threshQ; simp only [show x.biasedExp.val ≥ 1023 from by omega, ↓reduceIte]
    calc (2:ℚ)^(x.biasedExp.val - 1023)
        = 2^52 * 2^(x.biasedExp.val - 1075) := by rw [← pow_add]; congr 1; omega
      _ ≤ ↑x.effectiveSignificand * 2^(x.biasedExp.val - 1075) :=
          mul_le_mul_of_nonneg_right hesig (by positivity)
  · push_neg at hexp
    simp only [if_neg (show ¬(x.effectiveBinaryExp ≥ 0) from by omega)]
    have hblt : x.biasedExp.val < 1075 := by rw [hebe] at hexp; omega
    have htonat : (-x.effectiveBinaryExp).toNat = 1075 - x.biasedExp.val := by
      rw [hebe]; omega
    rw [htonat]
    unfold threshQ
    by_cases hge1023 : x.biasedExp.val ≥ 1023
    · simp only [show x.biasedExp.val ≥ 1023 from hge1023, ↓reduceIte]
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(1075 - x.biasedExp.val))]
      calc (2:ℚ)^(x.biasedExp.val - 1023) * 2^(1075 - x.biasedExp.val)
          = 2^52 := by rw [← pow_add]; congr 1; omega
        _ ≤ ↑x.effectiveSignificand := hesig
    · push_neg at hge1023
      simp only [show ¬(x.biasedExp.val ≥ 1023) from by omega, ↓reduceIte]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (2:ℚ)^(1075 - x.biasedExp.val)
          = 2^52 * 2^(1023 - x.biasedExp.val) := by rw [← pow_add]; congr 1; omega
        _ ≤ ↑x.effectiveSignificand * 2^(1023 - x.biasedExp.val) :=
            mul_le_mul_of_nonneg_right hesig (by positivity)

private theorem upper_bound_sub (x : F64) (hfin : x.isFinite)
    (hbexp : x.biasedExp.val = 0) (_hne : x.toRat ≠ 0) :
    |x.toRat| < threshQ 1 := by
  rw [toRat_abs x hfin]
  have hesig := esig_lt_52_sub x hbexp
  have hebe : x.effectiveBinaryExp = -1074 := by
    unfold effectiveBinaryExp expBias mantBits; simp [hbexp]
  simp only [hebe, show ¬((-1074 : Int) ≥ 0) from by omega, ↓reduceIte]
  have : (-(-1074 : Int)).toNat = 1074 := by omega
  rw [this]
  unfold threshQ; simp only [show ¬(1 ≥ 1023) from by omega, ↓reduceIte,
                              show 1023 - 1 = 1022 from by omega]
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  calc ↑x.effectiveSignificand * (2:ℚ)^1022
      < 2^52 * 2^1022 := mul_lt_mul_of_pos_right hesig (by positivity)
    _ = 2^1074 := by rw [← pow_add]

private theorem upper_bound_norm (x : F64) (hfin : x.isFinite) (hbexp : x.biasedExp.val ≥ 1) :
    |x.toRat| < threshQ (x.biasedExp.val + 1) := by
  rw [toRat_abs x hfin]
  have hesig := esig_lt_53 x
  have hbne : x.biasedExp.val ≠ 0 := by omega
  have hbexp_lt := finite_implies_exp_lt x hfin
  have hebe := ebe_normal x hbne
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    have hbge : x.biasedExp.val ≥ 1075 := by rw [hebe] at hexp; omega
    have htonat : x.effectiveBinaryExp.toNat = x.biasedExp.val - 1075 := by
      rw [hebe]; omega
    rw [htonat]
    unfold threshQ; simp only [show x.biasedExp.val + 1 ≥ 1023 from by omega, ↓reduceIte]
    calc ↑x.effectiveSignificand * (2:ℚ)^(x.biasedExp.val - 1075)
        < 2^53 * 2^(x.biasedExp.val - 1075) := mul_lt_mul_of_pos_right hesig (by positivity)
      _ = 2^(x.biasedExp.val + 1 - 1023) := by rw [← pow_add]; congr 1; omega
  · push_neg at hexp
    simp only [if_neg (show ¬(x.effectiveBinaryExp ≥ 0) from by omega)]
    have hblt : x.biasedExp.val < 1075 := by rw [hebe] at hexp; omega
    have htonat : (-x.effectiveBinaryExp).toNat = 1075 - x.biasedExp.val := by
      rw [hebe]; omega
    rw [htonat]
    unfold threshQ
    by_cases hge1022 : x.biasedExp.val + 1 ≥ 1023
    · simp only [show x.biasedExp.val + 1 ≥ 1023 from hge1022, ↓reduceIte]
      rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(1075 - x.biasedExp.val))]
      calc (↑x.effectiveSignificand : ℚ)
          < 2^53 := hesig
        _ = 2^(x.biasedExp.val + 1 - 1023) * 2^(1075 - x.biasedExp.val) := by
            rw [← pow_add]; congr 1; omega
    · push_neg at hge1022
      simp only [show ¬(x.biasedExp.val + 1 ≥ 1023) from by omega, ↓reduceIte]
      rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
      calc ↑x.effectiveSignificand * (2:ℚ)^(1023 - (x.biasedExp.val + 1))
          < 2^53 * 2^(1023 - (x.biasedExp.val + 1)) :=
            mul_lt_mul_of_pos_right hesig (by positivity)
        _ = 2^(1075 - x.biasedExp.val) := by rw [← pow_add]; congr 1; omega

/-- findBiasedExp correctly recovers the biased exponent. -/
theorem findBiasedExp_correct (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    findBiasedExp |x.toRat| = x.biasedExp.val := by
  unfold findBiasedExp
  have hexp_lt := finite_implies_exp_lt x hfin
  apply go_eq
  · omega
  · by_cases hbexp : x.biasedExp.val = 0
    · left; exact hbexp
    · right; exact lower_bound x hfin (by omega)
  · intro e hgt hle; push_neg
    by_cases hbexp : x.biasedExp.val = 0
    · calc |x.toRat| < threshQ 1 := upper_bound_sub x hfin hbexp hne
        _ ≤ threshQ e := threshQ_le_of_le (by omega)
    · calc |x.toRat| < threshQ (x.biasedExp.val + 1) := upper_bound_norm x hfin (by omega)
        _ ≤ threshQ e := threshQ_le_of_le (by omega)

/-! ## roundSignificand exactness -/

private theorem binExp_eq (x : F64) :
    (if x.biasedExp.val = 0 then (-1074 : Int) else (x.biasedExp.val : Int) - 1075) =
    x.effectiveBinaryExp := by
  unfold effectiveBinaryExp; simp only [expBias, mantBits]; split <;> omega

private theorem floor_nat_cast (n : Nat) : (n : ℚ).floor = (n : Int) := by
  change ⌊(↑n : ℚ)⌋ = ↑n; exact Int.floor_natCast n

private theorem sigExact_eq (x : F64) (hfin : x.isFinite) (_hne : x.toRat ≠ 0) :
    let binExp : Int := if x.biasedExp.val = 0 then -1074 else (x.biasedExp.val : Int) - 1075
    (if binExp ≥ 0 then |x.toRat| / (2 ^ binExp.toNat : ℚ)
     else |x.toRat| * (2 ^ (-binExp).toNat : ℚ)) =
    (x.effectiveSignificand : ℚ) := by
  simp only []
  rw [binExp_eq, toRat_abs x hfin]
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    exact mul_div_cancel_right₀ _ (ne_of_gt (by positivity))
  · simp only [if_neg hexp]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity))

private theorem esig_subnormal (x : F64) (h : x.biasedExp.val = 0) :
    x.effectiveSignificand = x.mantissa.val := by
  unfold effectiveSignificand; simp [h]

private theorem esig_normal (x : F64) (h : x.biasedExp.val ≠ 0) :
    x.effectiveSignificand = 2^52 + x.mantissa.val := by
  unfold effectiveSignificand; simp [h, mantBits]

/-- roundSignificand recovers the mantissa exactly with no bump. -/
theorem roundSignificand_exact (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundSignificand |x.toRat| x.biasedExp.val = (x.mantissa.val, false) := by
  unfold roundSignificand
  simp only []
  have hse := sigExact_eq x hfin hne
  simp only [] at hse
  rw [hse]
  rw [floor_nat_cast]
  simp only [Int.toNat_natCast]
  simp only [sub_self]
  norm_num
  have hm := x.mantissa.isLt
  split
  · next hbe =>
    have hbv : x.biasedExp.val = 0 := by simpa using congrArg Fin.val hbe
    rw [esig_subnormal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · next hbe =>
    have hbv : x.biasedExp.val ≠ 0 := fun h => hbe (Fin.ext h)
    rw [esig_normal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]
        constructor
        · omega
        · trivial

/-! ## Main composition -/

/-- roundToNearestEven(x.toRat) = x for finite non-zero x. -/
theorem round_nearest_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
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
  split
  · next h => exact absurd h (by decide)
  · split
    · next h => exfalso; unfold maxBiasedExp at h; omega
    · split
      · next hmk =>
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
      · next hmk =>
        exfalso; unfold mkFinite at hmk
        simp [show x.biasedExp.val < 2047 from hexp_lt] at hmk

end F64
