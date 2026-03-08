/-
  Ryu/Interval.lean

  The acceptance interval: for a finite F64 x, the set of rationals
  that round to x under round-to-nearest-even.
-/
import RyuLean4.IEEE754.RoundProof
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

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

/-! ## Helper lemmas -/

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

/-- The absolute interval has strictly positive bounds with low < high. -/
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
  · unfold schubfachInterval; simp only [hs, Bool.false_eq_true, ite_false]; exact key
  · unfold schubfachInterval; simp only [hs, Bool.true_eq_false, ite_false, ite_true, neg_neg]; exact key

/-! ## Core rounding lemma -/

/-- Rounding in [n - 1/2, n + 1/2] with tie-break to even gives n.
    This captures the essence of round-to-nearest-even: if the scaled
    significand falls within half a unit of n, rounding produces n
    (with correct tie-breaking at the boundaries). -/
private theorem round_in_half_interval (n : ℕ) (hn : n ≥ 1) (sigExact : ℚ)
    (hlo : (n : ℚ) - 1/2 ≤ sigExact)
    (hhi : sigExact ≤ (n : ℚ) + 1/2)
    (hlo_strict : sigExact = (n : ℚ) - 1/2 → n % 2 = 0)
    (hhi_strict : sigExact = (n : ℚ) + 1/2 → n % 2 = 0) :
    let sigFloor := sigExact.floor.toNat
    let remainder := sigExact - sigFloor
    (if remainder < 1/2 then sigFloor
     else if remainder > 1/2 then sigFloor + 1
     else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1) = n := by
  simp only []
  have hn_cast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    exact_mod_cast this
  by_cases hge : sigExact ≥ (n : ℚ)
  · have hfloor : sigExact.floor = (n : ℤ) := by
      show ⌊sigExact⌋ = ↑n
      rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast hge, by push_cast; linarith⟩
    have htonat : sigExact.floor.toNat = n := by omega
    rw [htonat]
    by_cases hrem_lt : sigExact - (n : ℚ) < 1/2
    · rw [if_pos hrem_lt]
    · push_neg at hrem_lt
      rw [if_neg (by linarith), if_neg (by linarith)]
      rw [if_pos (hhi_strict (by linarith))]
  · push_neg at hge
    have hfloor : sigExact.floor = (n : ℤ) - 1 := by
      show ⌊sigExact⌋ = ↑n - 1
      rw [Int.floor_eq_iff]; exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    have htonat : sigExact.floor.toNat = n - 1 := by omega
    rw [htonat]
    by_cases hrem_eq : sigExact = (n : ℚ) - 1/2
    · have hmod := hlo_strict hrem_eq
      have hmod1 : (n - 1) % 2 = 1 := by omega
      rw [if_neg (by rw [hrem_eq, hn_cast]; linarith)]
      rw [if_neg (by rw [hrem_eq, hn_cast]; linarith)]
      rw [if_neg (by rw [hmod1]; omega)]
      omega
    · have hlt : sigExact > (n : ℚ) - 1/2 := lt_of_le_of_ne hlo (Ne.symm hrem_eq)
      have hrem_gt : sigExact - ((n - 1 : ℕ) : ℚ) > 1/2 := by rw [hn_cast]; linarith
      rw [if_neg (by linarith), if_pos hrem_gt]
      omega

/-! ## Decomposing roundSignificand -/

/-- The rounding step of roundSignificand: compute sigExact, round to nearest even. -/
private def sigRoundedOf (qAbs : ℚ) (bexp : Nat) : Nat :=
  let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
  let sigExact : ℚ := if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
                       else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  if remainder < 1/2 then sigFloor
  else if remainder > 1/2 then sigFloor + 1
  else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1

/-- The branch analysis: convert sigRounded to (mantissa, bumpExp). -/
private def branchOf (sigRounded : Nat) (bexp : Nat) : Nat × Bool :=
  if bexp = 0 then
    if sigRounded ≥ 2^52 then (sigRounded - 2^52, true) else (sigRounded, false)
  else
    if sigRounded ≥ 2 * 2^52 then (sigRounded / 2 - 2^52, true)
    else if sigRounded < 2^52 then (sigRounded, false)
    else (sigRounded - 2^52, false)

private theorem roundSignificand_split (qAbs : ℚ) (bexp : Nat) :
    F64.roundSignificand qAbs bexp = branchOf (sigRoundedOf qAbs bexp) bexp := rfl

private theorem branchOf_mf (x : F64) :
    branchOf x.effectiveSignificand x.biasedExp.val = (x.mantissa.val, false) := by
  unfold branchOf
  have hm := x.mantissa.isLt
  split
  · next hbe =>
    rw [F64.esig_subnormal x (by omega)]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · next hbe =>
    rw [F64.esig_normal x (by omega)]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]; exact ⟨by omega, trivial⟩

/-! ## Scaling lemmas -/

private theorem pow_ef_cancel (ef : Int) (hef2 : ¬(ef - 2 ≥ 0)) (hef : ef ≥ 0) :
    (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = 4 := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem pow_ef_cancel_neg (ef : Int) (hef : ef < 0) :
    (2:ℚ) ^ (-ef).toNat * 4 = 2 ^ (-(ef - 2)).toNat := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem sigExact_lower_bound (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat) ≤ qAbs) :
    (n : ℚ) / 4 ≤
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    linarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right hle (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_iff₀ (by norm_num : (0:ℚ) < 4)]
      linarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg ef (by omega)]]

private theorem sigExact_upper_bound (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs ≤ (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) ≤ (n : ℚ) / 4 := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    linarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hge := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [mul_le_mul_of_nonneg_right hge (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hge := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [le_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      linarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg ef (by omega)]]

private theorem sigExact_lower_bound_strict (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat) < qAbs) :
    (n : ℚ) / 4 <
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_right hlt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg ef (by omega)]]

private theorem sigExact_upper_bound_strict (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs < (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) < (n : ℚ) / 4 := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hgt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_lt_mul_of_pos_right hgt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hgt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [lt_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg ef (by omega)]]

/-- sigRoundedOf = effectiveSignificand when sigExact ∈ [mf - 1/2, mf + 1/2]. -/
private theorem sigRoundedOf_from_bounds (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (qAbs : ℚ)
    (hsig_lo : (x.effectiveSignificand : ℚ) - 1/2 ≤
      (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat))
    (hsig_hi : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) ≤
      (x.effectiveSignificand : ℚ) + 1/2)
    (hlo_even : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) =
      (x.effectiveSignificand : ℚ) - 1/2 → x.effectiveSignificand % 2 = 0)
    (hhi_even : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) =
      (x.effectiveSignificand : ℚ) + 1/2 → x.effectiveSignificand % 2 = 0) :
    sigRoundedOf qAbs x.biasedExp.val = x.effectiveSignificand := by
  unfold sigRoundedOf; simp only []; rw [F64.binExp_eq]
  exact round_in_half_interval x.effectiveSignificand
    (effSig_pos_of_toRat_ne_zero x hfin hne) _ hsig_lo hsig_hi hlo_even hhi_even

/-! ## Interval soundness -/

/-! ### Case A: same biased exponent -/

/-- Case A: when findBiasedExp returns the same exponent as x,
    roundSignificand recovers x's mantissa. -/
private theorem interval_round_same_exp (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe : F64.findBiasedExp |q| = x.biasedExp.val) :
    F64.roundToNearestEven q = x := by
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  unfold F64.roundToNearestEven
  rw [if_neg hq_ne]
  simp only []
  rw [hfbe]
  have hrs : F64.roundSignificand |q| x.biasedExp.val = (x.mantissa.val, false) := by
    rw [roundSignificand_split]
    set mf := x.effectiveSignificand
    set ef := x.effectiveBinaryExp
    set e2 := ef - 2
    set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat)
    set u := 4 * mf - delta
    set w := 4 * mf + 2
    have hmf_pos := effSig_pos_of_toRat_ne_zero x hfin hne
    have hdelta_le : delta ≤ 2 := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 2; split <;> omega
    -- Extract |q| bounds from interval membership
    have habs_lo : (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat
                    else (u : ℚ) / 2 ^ (-e2).toNat) ≤ |q| := by
      unfold AcceptanceInterval.contains schubfachInterval at hq
      simp only [] at hq
      cases hs : x.sign
      · have hq_pos : 0 < q := by
          have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
          exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
        rw [abs_of_pos hq_pos]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨hlo, _⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
        · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
      · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
        rw [abs_of_neg hq_neg]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨_, hhi⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
        · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
    have habs_hi : |q| ≤ (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat
                           else (w : ℚ) / 2 ^ (-e2).toNat) := by
      unfold AcceptanceInterval.contains schubfachInterval at hq
      simp only [] at hq
      cases hs : x.sign
      · have hq_pos : 0 < q := by
          have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
          exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
        rw [abs_of_pos hq_pos]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨_, hhi⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
        · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
      · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
        rw [abs_of_neg hq_neg]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨hlo, _⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
        · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
    -- Apply scaling lemmas
    have hsig_lo := sigExact_lower_bound u |q| ef habs_lo
    have hsig_hi := sigExact_upper_bound w |q| ef habs_hi
    -- u/4 ≥ mf - 1/2
    have hu_lower : (mf : ℚ) - 1/2 ≤ (u : ℚ) / 4 := by
      have hsub : delta ≤ 4 * mf := by
        show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 4 * mf
        split <;> omega
      show (mf : ℚ) - 1/2 ≤ ((4 * mf - delta : ℕ) : ℚ) / 4
      push_cast [Nat.cast_sub hsub]
      linarith [show (delta : ℚ) ≤ 2 from by exact_mod_cast hdelta_le]
    -- w/4 = mf + 1/2
    have hw_eq : (w : ℚ) / 4 = (mf : ℚ) + 1/2 := by
      show ((4 * mf + 2 : ℕ) : ℚ) / 4 = (mf : ℚ) + 1/2; push_cast; ring
    -- Tie-breaking: lower boundary
    have hlo_even : (if ef ≥ 0 then |q| / (2:ℚ) ^ ef.toNat
                     else |q| * (2:ℚ) ^ (-ef).toNat) =
                    (mf : ℚ) - 1/2 → mf % 2 = 0 := by
      intro heq
      have hu_eq : (u : ℚ) / 4 = (mf : ℚ) - 1/2 :=
        le_antisymm (by linarith [heq, hsig_lo]) hu_lower
      have hdelta2 : delta = 2 := by
        have hsub : delta ≤ 4 * mf := by
          show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 4 * mf
          split <;> omega
        have h_eq : (u : ℚ) = ((4 * mf - delta : ℕ) : ℚ) := by rfl
        rw [h_eq] at hu_eq
        push_cast [Nat.cast_sub hsub] at hu_eq
        have : (delta : ℚ) = 2 := by linarith
        exact_mod_cast this
      by_contra h_not_even
      have h_odd : x.mantissa.val % 2 ≠ 0 := by
        by_cases hbexp : x.biasedExp.val = 0
        · rwa [show mf = x.mantissa.val from F64.esig_subnormal x hbexp] at h_not_even
        · rw [show mf = 2^52 + x.mantissa.val from F64.esig_normal x hbexp] at h_not_even
          intro h; exact h_not_even (by omega)
      -- Extract strict lower bound from interval with odd mantissa
      have habs_strict : (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat
                          else (u : ℚ) / 2 ^ (-e2).toNat) < |q| := by
        unfold AcceptanceInterval.contains schubfachInterval at hq
        simp only [] at hq
        cases hs : x.sign
        · have hq_pos : 0 < q := by
            have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
            exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
          rw [abs_of_pos hq_pos]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨hlo, _⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
          · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
        · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
          rw [abs_of_neg hq_neg]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨_, hhi⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
          · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
      linarith [sigExact_lower_bound_strict u |q| ef habs_strict]
    -- Tie-breaking: upper boundary
    have hhi_even : (if ef ≥ 0 then |q| / (2:ℚ) ^ ef.toNat
                     else |q| * (2:ℚ) ^ (-ef).toNat) =
                    (mf : ℚ) + 1/2 → mf % 2 = 0 := by
      intro heq
      by_contra h_not_even
      have h_odd : x.mantissa.val % 2 ≠ 0 := by
        by_cases hbexp : x.biasedExp.val = 0
        · rwa [show mf = x.mantissa.val from F64.esig_subnormal x hbexp] at h_not_even
        · rw [show mf = 2^52 + x.mantissa.val from F64.esig_normal x hbexp] at h_not_even
          intro h; exact h_not_even (by omega)
      -- Extract strict upper bound
      have habs_strict : |q| < (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat
                                else (w : ℚ) / 2 ^ (-e2).toNat) := by
        unfold AcceptanceInterval.contains schubfachInterval at hq
        simp only [] at hq
        cases hs : x.sign
        · have hq_pos : 0 < q := by
            have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
            exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
          rw [abs_of_pos hq_pos]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨_, hhi⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
          · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
        · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
          rw [abs_of_neg hq_neg]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨hlo, _⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
          · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
      linarith [sigExact_upper_bound_strict w |q| ef habs_strict]
    -- Apply sigRoundedOf_from_bounds
    have hsig := sigRoundedOf_from_bounds x hfin hne |q|
      (le_trans hu_lower hsig_lo) (by rw [← hw_eq]; exact hsig_hi)
      hlo_even hhi_even
    rw [hsig]
    exact branchOf_mf x
  -- Step 2: Use hrs to finish
  rw [hrs]
  simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold F64.maxBiasedExp; omega)]
  unfold F64.mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt,
             show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
  rw [hdec]

/-! ### Case B: boundary case -/

private theorem pos_of_sign_false {x : F64} (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign) (hs : x.sign = false) : 0 < q := by
  have h1 : decide (q < 0) = false := hdec.trans hs
  have hnneg : ¬(q < 0) := decide_eq_false_iff_not.mp h1
  exact lt_of_le_of_ne (not_lt.mp hnneg) (Ne.symm hq_ne)

private theorem neg_of_sign_true {x : F64} (q : ℚ)
    (hdec : decide (q < 0) = x.sign) (hs : x.sign = true) : q < 0 := by
  have h1 : decide (q < 0) = true := hdec.trans hs
  exact decide_eq_true_iff.mp h1

/-- Extract |q| bounds from schubfachInterval. -/
private theorem interval_abs_bounds (x : F64) (hfin : x.isFinite)
    (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q) :
    let mf := x.effectiveSignificand
    let e2 := x.effectiveBinaryExp - 2
    let delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat)
    let u := 4 * mf - delta
    let w := 4 * mf + 2
    (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat else (u : ℚ) / 2 ^ (-e2).toNat) ≤ |q| ∧
    |q| ≤ (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat else (w : ℚ) / 2 ^ (-e2).toNat) := by
  simp only []
  unfold AcceptanceInterval.contains schubfachInterval at hq; simp only [] at hq
  cases hs : x.sign
  · have hq_pos := pos_of_sign_false q hq_ne hdec hs
    rw [abs_of_pos hq_pos]
    simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hq
    obtain ⟨hlo, hhi⟩ := hq
    constructor
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
      · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
      · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
  · have hq_neg := neg_of_sign_true q hdec hs
    rw [abs_of_neg hq_neg]
    simp only [hs, Bool.true_eq_false, ite_true] at hq
    obtain ⟨hlo, hhi⟩ := hq
    constructor
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
      · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
      · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith

/-- If u ≥ 2^54 and e2 = be - 1077, then scaleN(u, e2) ≥ threshQ(be). -/
private theorem scaleN_ge_threshQ (u : Nat) (be : Nat) (hu : u ≥ 2^54)
    (hbe_ge : be ≥ 1) (hbe_lt : be < 2047) :
    let e2 : Int := (be : Int) - 1077
    F64.threshQ be ≤ (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat else (u : ℚ) / 2 ^ (-e2).toNat) := by
  simp only []
  by_cases hge1077 : (be : Int) - 1077 ≥ 0
  · simp only [if_pos hge1077]
    have htonat : ((be : Int) - 1077).toNat = be - 1077 := by omega
    rw [htonat]
    unfold F64.threshQ; simp only [show be ≥ 1023 from by omega, ↓reduceIte]
    calc (2:ℚ) ^ (be - 1023)
        = 2^54 * 2^(be - 1077) := by rw [← pow_add]; congr 1; omega
      _ ≤ (u : ℚ) * 2^(be - 1077) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hu
  · push_neg at hge1077
    simp only [show ¬((be : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 1077)).toNat = 1077 - be := by omega
    rw [htonat]
    unfold F64.threshQ
    by_cases hge1023 : be ≥ 1023
    · simp only [show be ≥ 1023 from hge1023, ↓reduceIte]
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(1077 - be))]
      calc (2:ℚ) ^ (be - 1023) * 2^(1077 - be) = 2^54 := by rw [← pow_add]; congr 1; omega
        _ ≤ (u : ℚ) := by exact_mod_cast hu
    · push_neg at hge1023
      simp only [show ¬(be ≥ 1023) from by omega, ↓reduceIte]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (2:ℚ) ^ (1077 - be)
          = 2^54 * 2^(1023 - be) := by rw [← pow_add]; congr 1; omega
        _ ≤ (u : ℚ) * 2^(1023 - be) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hu

/-- If w < 2^55 and e2 = be - 1077, then scaleN(w, e2) < threshQ(be+1). -/
private theorem scaleN_lt_threshQ_succ (w : Nat) (be : Nat) (hw : (w : ℚ) < 2^55)
    (hbe_ge : be ≥ 1) (hbe_lt : be < 2047) :
    let e2 : Int := (be : Int) - 1077
    (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat else (w : ℚ) / 2 ^ (-e2).toNat) < F64.threshQ (be + 1) := by
  simp only []
  by_cases hge1077 : (be : Int) - 1077 ≥ 0
  · simp only [if_pos hge1077]
    have htonat : ((be : Int) - 1077).toNat = be - 1077 := by omega
    rw [htonat]
    unfold F64.threshQ; simp only [show be + 1 ≥ 1023 from by omega, ↓reduceIte]
    calc (w : ℚ) * 2^(be - 1077)
        < 2^55 * 2^(be - 1077) := mul_lt_mul_of_pos_right hw (by positivity)
      _ = 2^(be + 1 - 1023) := by rw [← pow_add]; congr 1; omega
  · push_neg at hge1077
    simp only [show ¬((be : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 1077)).toNat = 1077 - be := by omega
    rw [htonat]
    unfold F64.threshQ
    by_cases hge1022 : be + 1 ≥ 1023
    · simp only [show be + 1 ≥ 1023 from hge1022, ↓reduceIte]
      rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(1077 - be))]
      calc (w : ℚ) < 2^55 := hw
        _ = 2^(be + 1 - 1023) * 2^(1077 - be) := by rw [← pow_add]; congr 1; omega
    · push_neg at hge1022
      simp only [show ¬(be + 1 ≥ 1023) from by omega, ↓reduceIte]
      rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (w : ℚ) * 2^(1023 - (be + 1))
          < 2^55 * 2^(1023 - (be + 1)) := mul_lt_mul_of_pos_right hw (by positivity)
        _ = 2^(1077 - be) := by rw [← pow_add]; congr 1; omega

/-! #### Step 1: biasedExp ≥ 1 -/

private theorem boundary_bexp_ge_one (x : F64) (hfin : x.isFinite) (_hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    x.biasedExp.val ≥ 1 := by
  by_contra hlt; push_neg at hlt
  have hbexp0 : x.biasedExp.val = 0 := by omega
  have hesig_lt := F64.esig_lt_52_sub x hbexp0
  have hebe : x.effectiveBinaryExp = -1074 := by
    unfold F64.effectiveBinaryExp F64.expBias F64.mantBits; simp [hbexp0]
  have he2 : x.effectiveBinaryExp - 2 = -1076 := by rw [hebe]; ring
  have ⟨_, habs_hi⟩ := interval_abs_bounds x hfin q hq_ne hdec hq
  simp only [he2, show ¬((-1076 : Int) ≥ 0) from by omega, ↓reduceIte,
             show ((-(-1076 : Int)).toNat) = 1076 from by omega] at habs_hi
  have hesig_nat : x.effectiveSignificand < 2^52 := by exact_mod_cast hesig_lt
  have hw_bound : (4 * x.effectiveSignificand + 2 : ℚ) ≤ 2^54 - 2 := by
    have hle : (x.effectiveSignificand : ℤ) ≤ (2^52 : ℤ) - 1 := by omega
    have : (x.effectiveSignificand : ℚ) ≤ 2^52 - 1 := by exact_mod_cast hle
    linarith
  have hq_lt : |q| < F64.threshQ 1 := by
    unfold F64.threshQ; simp only [show ¬(1 ≥ 1023) from by omega, ↓reduceIte,
                                   show 1023 - 1 = 1022 from by omega]
    calc |q| ≤ (↑(4 * x.effectiveSignificand + 2)) / 2^1076 := habs_hi
      _ ≤ (2^54 - 2 : ℚ) / 2^1076 :=
          div_le_div_of_nonneg_right (by exact_mod_cast (show (4 * x.effectiveSignificand + 2 : ℤ) ≤ (2^54 : ℤ) - 2 from by omega)) (by positivity)
      _ < 1 / 2^1022 := by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
  have hfbe_zero : F64.findBiasedExp |q| = 0 := by
    unfold F64.findBiasedExp
    apply F64.go_eq
    · omega
    · left; rfl
    · intro e he hle; push_neg
      calc |q| < F64.threshQ 1 := hq_lt
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  rw [hfbe_zero, hbexp0] at hfbe_ne
  exact absurd rfl hfbe_ne

/-! #### Step 1b: mantissa = 0 -/

private theorem boundary_mant_zero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    x.mantissa.val = 0 := by
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  by_contra hmant_ne
  have hesig := F64.esig_normal x (by omega : x.biasedExp.val ≠ 0)
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) = 2 := by
    simp [hmant_ne]
  -- u ≥ 2^54 + 2 > 2^54
  have hu_ge : 4 * x.effectiveSignificand - 2 ≥ 2^54 + 2 := by rw [hesig]; omega
  -- Get bounds
  have ⟨habs_lo, habs_hi⟩ := interval_abs_bounds x hfin q hq_ne hdec hq
  simp only [hdelta] at habs_lo
  rw [he2] at habs_lo habs_hi
  -- |q| ≥ threshQ(biasedExp)
  have hscaleN_ge := scaleN_ge_threshQ (4 * x.effectiveSignificand - 2) x.biasedExp.val
    (by omega) hbexp hexp_lt
  rw [show ((x.biasedExp.val : Int) - 1077) = (x.biasedExp.val : Int) - 1077 from rfl] at hscaleN_ge
  have hge_thresh : F64.threshQ x.biasedExp.val ≤ |q| := le_trans hscaleN_ge habs_lo
  -- |q| < threshQ(biasedExp + 1) using w < 2^55
  have hesig_lt := F64.esig_lt_53 x
  have hw_lt : (4 * x.effectiveSignificand + 2 : ℚ) < 2^55 := by
    have hesig_nat : x.effectiveSignificand < 2^53 := by exact_mod_cast hesig_lt
    have : (x.effectiveSignificand : ℚ) ≤ 2^53 - 1 := by
      exact_mod_cast (show (x.effectiveSignificand : ℤ) ≤ (2^53 : ℤ) - 1 from by omega)
    linarith
  have hlt_thresh := scaleN_lt_threshQ_succ (4 * x.effectiveSignificand + 2) x.biasedExp.val
    (by exact_mod_cast hw_lt) hbexp hexp_lt
  have hlt_thresh_q : |q| < F64.threshQ (x.biasedExp.val + 1) :=
    lt_of_le_of_lt habs_hi hlt_thresh
  -- findBiasedExp = biasedExp
  have hfbe : F64.findBiasedExp |q| = x.biasedExp.val := by
    unfold F64.findBiasedExp
    apply F64.go_eq
    · omega
    · right; exact hge_thresh
    · intro e hgt hle; push_neg
      calc |q| < F64.threshQ (x.biasedExp.val + 1) := hlt_thresh_q
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  exact absurd hfbe hfbe_ne

/-! #### Step 2: |q| < threshQ(biasedExp) -/

private theorem boundary_qabs_lt_thresh (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    |q| < F64.threshQ x.biasedExp.val := by
  by_contra hge; push_neg at hge
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have ⟨_, habs_hi⟩ := interval_abs_bounds x hfin q hq_ne hdec hq
  rw [hesig_val, he2] at habs_hi
  -- w = 2^54 + 2 < 2^55
  have hw_lt : ((4 * (2:Nat)^52 + 2 : Nat) : ℚ) < 2^55 := by norm_num
  have hlt_thresh := scaleN_lt_threshQ_succ (4 * 2^52 + 2) x.biasedExp.val hw_lt hbexp hexp_lt
  have : |q| < F64.threshQ (x.biasedExp.val + 1) := lt_of_le_of_lt habs_hi hlt_thresh
  -- findBiasedExp = biasedExp
  have hfbe_eq : F64.findBiasedExp |q| = x.biasedExp.val := by
    unfold F64.findBiasedExp
    apply F64.go_eq
    · omega
    · right; exact hge
    · intro e hgt hle; push_neg
      calc |q| < F64.threshQ (x.biasedExp.val + 1) := this
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  exact absurd hfbe_eq hfbe_ne

/-! #### Step 2b: |q| ≥ threshQ(biasedExp - 1) -/

private theorem boundary_qabs_ge_prev (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    F64.threshQ (x.biasedExp.val - 1) ≤ |q| := by
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) =
      if x.biasedExp.val > 1 then 1 else 2 := by simp [hmant]
  have ⟨habs_lo, _⟩ := interval_abs_bounds x hfin q hq_ne hdec hq
  rw [hdelta, hesig_val, he2] at habs_lo
  apply le_trans _ habs_lo
  by_cases hbe1 : x.biasedExp.val = 1
  · have he2_val : (x.biasedExp.val : Int) - 1077 = -1076 := by omega
    rw [he2_val, hbe1]
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte,
               show (4 * (2:Nat)^52 - 2) = (2^54 - 2 : Nat) from by norm_num,
               show ¬((-1076 : Int) ≥ 0) from by omega,
               show ((-(-1076 : Int)).toNat) = 1076 from by omega,
               show 1 - 1 = 0 from by omega]
    unfold F64.threshQ; simp only [show ¬(0 ≥ 1023) from by omega, ↓reduceIte,
                                   show 1023 - 0 = 1023 from by omega]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    norm_num
  · have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    simp only [show x.biasedExp.val > 1 from by omega, ↓reduceIte,
               show (4 * (2:Nat)^52 - 1) = (2^54 - 1 : Nat) from by norm_num]
    by_cases hge1077 : (x.biasedExp.val : Int) - 1077 ≥ 0
    · simp only [if_pos hge1077]
      have htonat : ((x.biasedExp.val : Int) - 1077).toNat = x.biasedExp.val - 1077 := by omega
      rw [htonat]
      unfold F64.threshQ; simp only [show x.biasedExp.val - 1 ≥ 1023 from by omega, ↓reduceIte]
      calc (2:ℚ) ^ (x.biasedExp.val - 1 - 1023)
          = 2^53 * 2^(x.biasedExp.val - 1077) := by rw [← pow_add]; congr 1; omega
        _ ≤ ((2^54 - 1 : Nat) : ℚ) * 2^(x.biasedExp.val - 1077) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    · push_neg at hge1077
      simp only [show ¬((x.biasedExp.val : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
      have htonat : (-((x.biasedExp.val : Int) - 1077)).toNat = 1077 - x.biasedExp.val := by omega
      rw [htonat]
      unfold F64.threshQ
      by_cases hge1024 : x.biasedExp.val - 1 ≥ 1023
      · simp only [show x.biasedExp.val - 1 ≥ 1023 from hge1024, ↓reduceIte]
        rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(1077 - x.biasedExp.val))]
        calc (2:ℚ) ^ (x.biasedExp.val - 1 - 1023) * 2^(1077 - x.biasedExp.val)
            = 2^53 := by rw [← pow_add]; congr 1; omega
          _ ≤ ((2^54 - 1 : Nat) : ℚ) := by norm_num
      · push_neg at hge1024
        simp only [show ¬(x.biasedExp.val - 1 ≥ 1023) from by omega, ↓reduceIte]
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        calc (2:ℚ) ^ (1077 - x.biasedExp.val)
            = 2^53 * 2^(1023 - (x.biasedExp.val - 1)) := by rw [← pow_add]; congr 1; omega
          _ ≤ ((2^54 - 1 : Nat) : ℚ) * 2^(1023 - (x.biasedExp.val - 1)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-! #### Step 2c: findBiasedExp = biasedExp - 1 -/

private theorem boundary_fbe_eq (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    F64.findBiasedExp |q| = x.biasedExp.val - 1 := by
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  have hqlt := boundary_qabs_lt_thresh x hfin hne q hq_ne hdec hq hfbe_ne
  have hqge := boundary_qabs_ge_prev x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  unfold F64.findBiasedExp
  apply F64.go_eq
  · omega
  · by_cases hbe1 : x.biasedExp.val = 1
    · left; omega
    · right; exact hqge
  · intro e he hle; push_neg
    calc |q| < F64.threshQ x.biasedExp.val := hqlt
      _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)

/-! #### Step 3: roundSignificand(|q|, biasedExp - 1) = (0, true) -/

/-- Helper: if sigExact ∈ [N - 1/2, N) with N-1 odd, then the rounding gives N. -/
private theorem round_to_N (N : Nat) (sigExact : ℚ)
    (hlo : (N : ℚ) - 1/2 ≤ sigExact) (hhi : sigExact < N)
    (hN_ge : N ≥ 2) (hN_odd_pred : (N - 1) % 2 = 1) :
    let sigFloor := sigExact.floor.toNat
    let remainder := sigExact - sigFloor
    (if remainder < 1/2 then sigFloor
     else if remainder > 1/2 then sigFloor + 1
     else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1) = N := by
  simp only []
  -- floor = N - 1
  have hfloor : sigExact.floor = ((N : Int) - 1) := by
    rw [show sigExact.floor = ⌊sigExact⌋ from rfl, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have htonat : sigExact.floor.toNat = N - 1 := by rw [hfloor]; omega
  rw [htonat]
  -- remainder ≥ 1/2
  have hrem_ge : sigExact - ((N - 1 : Nat) : ℚ) ≥ 1/2 := by
    have : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
      have : ((N - 1 : Nat) : ℤ) = (N : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [this]; linarith
  rw [if_neg (by linarith)]
  by_cases hrem_gt : sigExact - ((N - 1 : Nat) : ℚ) > 1/2
  · rw [if_pos hrem_gt]; omega
  · push_neg at hrem_gt
    rw [if_neg (by linarith)]
    -- floor = N-1, which is odd
    rw [if_neg (by omega)]
    omega

/-- If the sigExact inside sigRoundedOf lies in [N - 1/2, N) with N ≥ 2 and (N-1) odd,
    then sigRoundedOf = N. This is a thin wrapper that unfolds sigRoundedOf and
    applies round_to_N. -/
private theorem sigRoundedOf_eq_of_bounds (qAbs : ℚ) (bexp N : Nat)
    (hN_ge : N ≥ 2) (hN_odd_pred : (N - 1) % 2 = 1)
    (hlo : (N : ℚ) - 1/2 ≤
      let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
      if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
      else qAbs * (2 ^ (-binExp).toNat : ℚ))
    (hhi :
      (let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
      if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
      else qAbs * (2 ^ (-binExp).toNat : ℚ)) < N) :
    sigRoundedOf qAbs bexp = N := by
  unfold sigRoundedOf
  simp only [] at hlo hhi ⊢
  exact round_to_N N _ hlo hhi hN_ge hN_odd_pred

/-- Convert interval lower bound to sigExact lower bound for bexp=1 (subnormal boundary).
    The interval gives (4·2^52-2)/2^1076 ≤ |q|, and sigExact = |q|·2^1074,
    so sigExact ≥ (4·2^52-2)/4 = 2^52 - 1/2. -/
private theorem boundary_sigExact_lo_sub (qAbs : ℚ)
    (habs_lo : ((4 * 2 ^ 52 - 2 : Nat) : ℚ) / 2 ^ 1076 ≤ qAbs) :
    (2^52 : ℚ) - 1/2 ≤ qAbs * 2^1074 := by
  have hscale : ((4 * 2^52 - 2 : Nat) : ℚ) / 2^1076 * 2^1074 = 2^52 - 1/2 := by
    have h1 : (2:ℚ)^1076 = 2^2 * 2^1074 := by rw [← pow_add]
    rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^1074 ≠ 0)]
    push_cast; norm_num
  linarith [mul_le_mul_of_nonneg_right habs_lo (show (0:ℚ) ≤ 2^1074 from by positivity)]

/-- Convert threshQ upper bound to sigExact upper bound for bexp=1.
    threshQ(1) = 1/2^1022, sigExact = |q|·2^1074, so sigExact < 2^52. -/
private theorem boundary_sigExact_hi_sub (qAbs : ℚ)
    (hqlt : qAbs < (1:ℚ) / 2^1022) :
    qAbs * 2^1074 < 2^52 := by
  have hscale : (1:ℚ) / 2^1022 * 2^1074 = 2^52 := by
    rw [one_div, inv_mul_eq_div]
    rw [show (2:ℚ)^1074 = 2^52 * 2^1022 from by rw [← pow_add]]
    rw [mul_div_cancel_right₀ _ (by positivity : (2:ℚ)^1022 ≠ 0)]
  linarith [mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^1074 from by positivity)]

/-- Convert interval lower bound to sigExact lower bound for bexp≥2 (normal boundary).
    In all sub-cases, the interval gives (2^54-1)·scale ≤ |q| and sigExact = |q|/scale',
    yielding sigExact ≥ (2^54-1)/2 = 2^53 - 1/2. -/
private theorem boundary_sigExact_lo_norm (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (habs_lo : (if (bexp : Int) - 1077 ≥ 0
      then ((2^54 - 1 : Nat) : ℚ) * 2^((bexp : Int) - 1077).toNat
      else ((2^54 - 1 : Nat) : ℚ) / 2^(-((bexp : Int) - 1077)).toNat) ≤ qAbs) :
    (2^53 : ℚ) - 1/2 ≤
      (if ((bexp : Int) - 1076 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 1076).toNat : ℚ)
       else qAbs * (2 ^ (-((bexp : Int) - 1076)).toNat : ℚ)) := by
  by_cases hbinexp_ge : (bexp : Int) - 1076 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 1076).toNat = bexp - 1076 := by omega
    rw [htonat]
    by_cases hge1077 : (bexp : Int) - 1077 ≥ 0
    · simp only [if_pos hge1077] at habs_lo
      have htonat2 : ((bexp : Int) - 1077).toNat = bexp - 1077 := by omega
      rw [htonat2] at habs_lo
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 1076))]
      calc ((2:ℚ)^53 - 1/2) * 2^(bexp - 1076)
          = ((2^54 - 1 : Nat) : ℚ) * 2^(bexp - 1077) := by
            push_cast
            rw [show (2:ℚ)^(bexp - 1076) = 2^1 * 2^(bexp - 1077) from by
              rw [← pow_add]; congr 1; omega]
            ring
        _ ≤ qAbs := habs_lo
    · push_neg at hge1077
      have hbe_eq : bexp = 1076 := by omega
      simp only [show ¬((bexp : Int) - 1077 ≥ 0) from by omega, ↓reduceIte] at habs_lo
      have htonat2 : (-((bexp : Int) - 1077)).toNat = 1077 - bexp := by omega
      rw [htonat2, hbe_eq] at habs_lo
      rw [hbe_eq, show 1076 - 1076 = 0 from by omega, pow_zero]
      simp only [div_one]
      have : ((2^54 - 1 : Nat) : ℚ) / 2 ^ 1 = 2^53 - 1/2 := by push_cast; norm_num
      linarith
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 1076 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 1076)).toNat = 1076 - bexp := by omega
    rw [htonat]
    have he2_neg : ¬((bexp : Int) - 1077 ≥ 0) := by omega
    simp only [he2_neg, ↓reduceIte] at habs_lo
    have htonat3 : (-((bexp : Int) - 1077)).toNat = 1077 - bexp := by omega
    rw [htonat3] at habs_lo
    have h := mul_le_mul_of_nonneg_right habs_lo (show (0:ℚ) ≤ 2^(1076 - bexp) from by positivity)
    calc (2^53 : ℚ) - 1/2
        = ((2^54 - 1 : Nat) : ℚ) / 2^(1077 - bexp) * 2^(1076 - bexp) := by
          push_cast
          have h1 : (2:ℚ)^(1077 - bexp) = 2^1 * 2^(1076 - bexp) := by
            rw [← pow_add]; congr 1; omega
          rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^(1076 - bexp) ≠ 0)]
          norm_num
      _ ≤ qAbs * 2^(1076 - bexp) := h

/-- Convert threshQ upper bound to sigExact upper bound for bexp≥2.
    In all sub-cases, threshQ(bexp)·(1/2^binExp) = 2^53, so sigExact < 2^53. -/
private theorem boundary_sigExact_hi_norm (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (hexp_lt : bexp < 2047)
    (hqlt : qAbs < F64.threshQ bexp) :
    (if ((bexp : Int) - 1076 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 1076).toNat : ℚ)
     else qAbs * (2 ^ (-((bexp : Int) - 1076)).toNat : ℚ)) < 2^53 := by
  by_cases hbinexp_ge : (bexp : Int) - 1076 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 1076).toNat = bexp - 1076 := by omega
    rw [htonat]
    unfold F64.threshQ at hqlt
    simp only [show bexp ≥ 1023 from by omega, ↓reduceIte] at hqlt
    rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 1076))]
    calc qAbs < 2^(bexp - 1023) := hqlt
      _ = 2^53 * 2^(bexp - 1076) := by rw [← pow_add]; congr 1; omega
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 1076 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 1076)).toNat = 1076 - bexp := by omega
    rw [htonat]
    unfold F64.threshQ at hqlt
    by_cases hge1023 : bexp ≥ 1023
    · simp only [show bexp ≥ 1023 from hge1023, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(1076 - bexp) from by positivity)
      calc qAbs * 2^(1076 - bexp)
        _ < 2^(bexp - 1023) * 2^(1076 - bexp) := h
        _ = 2^53 := by rw [← pow_add]; congr 1; omega
    · push_neg at hge1023
      simp only [show ¬(bexp ≥ 1023) from by omega, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(1076 - bexp) from by positivity)
      calc qAbs * 2^(1076 - bexp)
        _ < 1 / 2^(1023 - bexp) * 2^(1076 - bexp) := h
        _ = 2^53 := by
            rw [one_div, inv_mul_eq_div]
            rw [div_eq_iff (by positivity : (0:ℚ) < 2^(1023 - bexp)).ne']
            rw [← pow_add]; congr 1; omega

private theorem boundary_roundSig (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    F64.roundSignificand |q| (x.biasedExp.val - 1) = (0, true) := by
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero x hfin hne q hq_ne hdec hq hfbe_ne
  have hqlt := boundary_qabs_lt_thresh x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) =
      if x.biasedExp.val > 1 then 1 else 2 := by simp [hmant]
  have ⟨habs_lo, _⟩ := interval_abs_bounds x hfin q hq_ne hdec hq
  rw [hdelta, hesig_val, he2] at habs_lo
  rw [roundSignificand_split]
  by_cases hbe1 : x.biasedExp.val = 1
  · -- Case biasedExp = 1: roundSignificand(|q|, 0)
    simp only [hbe1, show 1 - 1 = 0 from by omega]
    suffices hsig : sigRoundedOf |q| 0 = 2^52 by
      rw [hsig]; unfold branchOf; simp
    have he2_val : (x.biasedExp.val : Int) - 1077 = -1076 := by omega
    rw [he2_val, hbe1] at habs_lo
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte,
               show ¬((-1076 : Int) ≥ 0) from by omega,
               show ((-(-1076 : Int)).toNat) = 1076 from by omega] at habs_lo
    rw [hbe1] at hqlt; unfold F64.threshQ at hqlt
    simp only [show ¬(1 ≥ 1023) from by omega, ↓reduceIte, show 1023 - 1 = 1022 from by omega] at hqlt
    exact sigRoundedOf_eq_of_bounds |q| 0 (2^52) (by norm_num) (by norm_num)
      (by simp only [↓reduceIte, show ¬((-1074 : Int) ≥ 0) from by omega,
                      show ((-(-1074 : Int)).toNat) = 1074 from by omega]
          exact boundary_sigExact_lo_sub |q| habs_lo)
      (by simp only [↓reduceIte, show ¬((-1074 : Int) ≥ 0) from by omega,
                      show ((-(-1074 : Int)).toNat) = 1074 from by omega]
          exact boundary_sigExact_hi_sub |q| hqlt)
  · -- Case biasedExp ≥ 2: roundSignificand(|q|, biasedExp-1)
    have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    have hbm1_ne0 : x.biasedExp.val - 1 ≠ 0 := by omega
    suffices hsig : sigRoundedOf |q| (x.biasedExp.val - 1) = 2^53 by
      rw [hsig]; unfold branchOf; simp only [hbm1_ne0, ↓reduceIte]; norm_num
    have hbinexp : ((x.biasedExp.val - 1 : Nat) : Int) - 1075 = (x.biasedExp.val : Int) - 1076 := by omega
    simp only [show x.biasedExp.val > 1 from by omega, ↓reduceIte,
               show (4 * (2:Nat)^52 - 1) = (2^54 - 1 : Nat) from by norm_num] at habs_lo
    exact sigRoundedOf_eq_of_bounds |q| (x.biasedExp.val - 1) (2^53) (by norm_num) (by norm_num)
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact boundary_sigExact_lo_norm x.biasedExp.val |q| hbe_ge2 habs_lo)
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact boundary_sigExact_hi_norm x.biasedExp.val |q| hbe_ge2 hexp_lt hqlt)

/-! #### Step 4: Assembly -/

/-- Case B: boundary case where findBiasedExp returns bexp-1.
    This happens only when mantissa=0 and the interval lower bound
    crosses the exponent threshold. The bump mechanism in
    roundSignificand corrects the exponent back to bexp. -/
private theorem interval_round_boundary (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q)
    (hfbe_ne : F64.findBiasedExp |q| ≠ x.biasedExp.val) :
    F64.roundToNearestEven q = x := by
  have hbexp := boundary_bexp_ge_one x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero x hfin hne q hq_ne hdec hq hfbe_ne
  have hfbe := boundary_fbe_eq x hfin hne q hq_ne hdec hq hfbe_ne
  have hrs := boundary_roundSig x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  unfold F64.roundToNearestEven
  rw [if_neg hq_ne]
  simp only []
  rw [hfbe, hrs]
  simp only [ite_true]
  have hfinalExp : x.biasedExp.val - 1 + 1 = x.biasedExp.val := by omega
  rw [hfinalExp]
  have hlt_max : ¬(x.biasedExp.val ≥ F64.maxBiasedExp) := by unfold F64.maxBiasedExp; omega
  rw [if_neg hlt_max]
  unfold F64.mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt, show (0:Nat) < 2^52 from by norm_num, dite_true]
  rw [hdec]
  rcases x with ⟨s, ⟨be, hbe_bound⟩, ⟨m, hm_bound⟩⟩
  rw [F64.mk.injEq]
  refine ⟨rfl, Fin.ext rfl, Fin.ext ?_⟩
  simp at hmant; exact hmant.symm

/-! ### Assembly -/

/-- Assembly: the acceptance interval is sound. -/
private theorem interval_round_core (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval x hfin).contains q) :
    F64.roundToNearestEven q = x := by
  by_cases hfbe : F64.findBiasedExp |q| = x.biasedExp.val
  · exact interval_round_same_exp x hfin hne q hq_ne hdec hq hfbe
  · exact interval_round_boundary x hfin hne q hq_ne hdec hq hfbe

/-- The acceptance interval is sound: any rational in the interval
    rounds to x. -/
theorem schubfach_interval_correct (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0)
    (q : ℚ) (hq : (schubfachInterval x hfin).contains q) :
    F64.roundToNearestEven q = x := by
  -- Step 1: q ≠ 0 (the interval for non-zero x doesn't contain 0)
  have hq_ne : q ≠ 0 := by
    intro heq; subst heq
    have ⟨hlo_pos, _⟩ := schubfach_abs_interval_pos x hfin hne
    unfold AcceptanceInterval.contains at hq
    cases hs : x.sign <;> simp [hs] at hlo_pos hq
    · obtain ⟨h, _⟩ := hq; split at h <;> linarith
    · obtain ⟨_, h⟩ := hq; split at h <;> linarith
  -- Step 2: sign of q matches x.sign
  have hdec : decide (q < 0) = x.sign := by
    have ⟨hlo_pos, _⟩ := schubfach_abs_interval_pos x hfin hne
    have hqc := hq
    unfold AcceptanceInterval.contains at hqc
    cases hs : x.sign <;> simp [hs] at hlo_pos hqc
    · obtain ⟨h, _⟩ := hqc
      have : 0 < q := by split at h <;> linarith
      exact decide_eq_false (by linarith)
    · obtain ⟨_, h⟩ := hqc
      have : q < 0 := by split at h <;> linarith
      exact decide_eq_true this
  exact interval_round_core x hfin hne q hq_ne hdec hq

end Ryu
