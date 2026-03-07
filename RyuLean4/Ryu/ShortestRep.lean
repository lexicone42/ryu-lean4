/-
  Ryu/ShortestRep.lean

  Find the shortest decimal representation in the acceptance interval.
-/
import RyuLean4.Ryu.Interval
import RyuLean4.Decimal.Decimal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option maxHeartbeats 800000

namespace Ryu

/-- A Decimal is a valid representation if it's in the acceptance interval. -/
def isValidRep (d : Decimal) (x : F64) (hfin : x.isFinite) : Prop :=
  (schubfachInterval x hfin).contains d.toRat

/-- A valid representation is shortest if no other valid one has fewer digits. -/
def isShortestRep (d : Decimal) (x : F64) (hfin : x.isFinite) : Prop :=
  isValidRep d x hfin ∧
  ∀ d' : Decimal, isValidRep d' x hfin → d.numDigits ≤ d'.numDigits

/-- Strip trailing zeros from a natural number.
    Returns (stripped, num_zeros_stripped). -/
def stripTrailingZeros (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else if n % 10 = 0 then
    let (n', e) := stripTrailingZeros (n / 10)
    (n', e + 1)
  else (n, 0)
termination_by n

theorem strip_no_trailing (n : Nat) :
    (stripTrailingZeros n).1 ≠ 0 → (stripTrailingZeros n).1 % 10 ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold stripTrailingZeros
    split
    · simp
    · next hn =>
      split
      · next hmod =>
        have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        show (stripTrailingZeros (n / 10)).1 ≠ 0 → (stripTrailingZeros (n / 10)).1 % 10 ≠ 0
        exact ih (n / 10) hdiv
      · next hmod =>
        simp only []
        intro; exact hmod

theorem strip_zero_iff (n : Nat) :
    (stripTrailingZeros n).1 = 0 ↔ n = 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold stripTrailingZeros
    split
    · next h => exact ⟨fun _ => h, fun _ => by simp⟩
    · next hn =>
      split
      · next hmod =>
        have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        show (stripTrailingZeros (n / 10)).1 = 0 ↔ n = 0
        rw [ih (n / 10) hdiv]
        constructor
        · intro h; omega
        · intro h; exact absurd h hn
      · simp [hn]

theorem strip_of_zero : stripTrailingZeros 0 = (0, 0) := by
  unfold stripTrailingZeros; simp

/-- Strip trailing zeros and produce a well-formed Decimal. -/
def mkStrippedDecimal (s : Bool) (d : Nat) (e : Int) : Decimal :=
  let p := stripTrailingZeros d
  if p.1 = 0 then ⟨s, 0, 0⟩
  else ⟨s, p.1, e + p.2⟩

theorem mkStrippedDecimal_well_formed (s : Bool) (d : Nat) (e : Int) :
    (mkStrippedDecimal s d e).WellFormed := by
  unfold mkStrippedDecimal
  simp only []
  split
  · exact ⟨fun h => absurd rfl h, fun _ => rfl⟩
  · next h =>
    exact ⟨fun _ => strip_no_trailing d h, fun h' => absurd h' h⟩

/-- Find shortest digit representation by trying increasing digit counts. -/
def findDigits (iv : AcceptanceInterval) (s : Bool)
    (absLow absHigh : ℚ) (n : Nat) (fuel : Nat) : Decimal :=
  match fuel with
  | 0 => ⟨false, 0, 0⟩
  | fuel' + 1 =>
    let scale : ℚ := 10 ^ (n - 1)
    let scaledLow := absLow * scale
    let scaledHigh := absHigh * scale
    let dLow : Nat := if iv.lowInclusive then
      scaledLow.ceil.toNat
    else
      scaledLow.floor.toNat + 1
    let dHigh : Nat := if iv.highInclusive then
      scaledHigh.floor.toNat
    else
      (scaledHigh.ceil - 1).toNat
    if dLow ≤ dHigh then
      let center := (absLow + absHigh) / 2
      let scaledCenter := center * scale
      let dCenter := scaledCenter.floor.toNat
      let d := max dLow (min dCenter dHigh)
      mkStrippedDecimal s d (-(n - 1 : Nat))
    else
      findDigits iv s absLow absHigh (n + 1) fuel'
termination_by fuel

theorem findDigits_well_formed (iv : AcceptanceInterval) (s : Bool)
    (absLow absHigh : ℚ) (n fuel : Nat) :
    (findDigits iv s absLow absHigh n fuel).WellFormed := by
  induction fuel generalizing n with
  | zero =>
    unfold findDigits
    exact ⟨fun h => absurd rfl h, fun _ => rfl⟩
  | succ fuel' ih =>
    unfold findDigits
    simp only []
    split <;> split <;> split <;> first
    | exact mkStrippedDecimal_well_formed _ _ _
    | exact ih (n + 1)

-- ============ Interval correctness helpers ============

private theorem rat_ceil_eq (q : ℚ) : q.ceil = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

private theorem strip_value (n : Nat) :
    (stripTrailingZeros n).1 * 10 ^ (stripTrailingZeros n).2 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold stripTrailingZeros
    split
    · next h => subst h; simp
    · next hn =>
      split
      · next hmod =>
        have hih := ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
        generalize hg : stripTrailingZeros (n / 10) = p at *
        show p.1 * 10 ^ (p.2 + 1) = n
        rw [Nat.pow_succ, ← Nat.mul_assoc, hih]; omega
      · exact Nat.mul_one n

private theorem val_div_eq {p1 p2 d k : Nat} (hval : (p1 : ℚ) * (10:ℚ)^p2 = (d : ℚ))
    (h10k : (10:ℚ)^k ≠ 0) :
    (p2 ≥ k → (p1 : ℚ) * (10:ℚ)^(p2 - k) = (d : ℚ) / (10:ℚ)^k) ∧
    (p2 < k → (p1 : ℚ) / (10:ℚ)^(k - p2) = (d : ℚ) / (10:ℚ)^k) := by
  constructor
  · intro hge
    rw [eq_div_iff h10k, mul_assoc, ← pow_add, show p2 - k + k = p2 from by omega, hval]
  · intro hlt
    rw [div_eq_div_iff (by positivity : (10:ℚ)^(k - p2) ≠ 0) h10k,
        show (p1 : ℚ) * 10^k = p1 * 10^(p2 + (k - p2)) from by
          rw [Nat.add_sub_cancel' (le_of_lt hlt)],
        pow_add, ← mul_assoc, hval]

private theorem mkStripped_toRat (s : Bool) (d : Nat) (k : Nat) (hd : d ≠ 0) :
    (mkStrippedDecimal s d (-(k:Nat))).toRat =
    (if s then -1 else 1) * ((d : ℚ) / (10:ℚ)^k) := by
  unfold mkStrippedDecimal; simp only []
  have hstrip_ne : (stripTrailingZeros d).1 ≠ 0 := (strip_zero_iff d).not.mpr hd
  rw [if_neg hstrip_ne]
  set p := stripTrailingZeros d
  have hval : (p.1 : ℚ) * (10:ℚ)^p.2 = (d : ℚ) := by exact_mod_cast strip_value d
  unfold Decimal.toRat; simp only []
  have h10k : (10:ℚ)^k ≠ 0 := by positivity
  have ⟨hge_case, hlt_case⟩ := val_div_eq hval h10k
  by_cases hexp : (-(k:Int) + (p.2:Int)) ≥ 0
  · rw [if_pos hexp, show (-(k:Int) + (p.2:Int)).toNat = p.2 - k from by omega]
    cases s <;> simp [hge_case (by omega)]
  · rw [if_neg (by omega : ¬(-(k:Int) + (p.2:Int)) ≥ 0),
        show (-(-(k:Int) + (p.2:Int))).toNat = k - p.2 from by omega]
    have hkey := hlt_case (by omega)
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; exact hkey
    · simp only [↓reduceIte]
      rw [show (-1:ℚ) * (p.1:ℚ) / (10:ℚ)^(k - p.2) =
            -1 * ((p.1:ℚ) / (10:ℚ)^(k - p.2)) from mul_div_assoc _ _ _, hkey]

private theorem ceil_toNat_le_imp (x : ℚ) (d : Nat) (_hx : 0 ≤ x) (h : x.ceil.toNat ≤ d) :
    x ≤ (d : ℚ) := by
  rw [rat_ceil_eq] at h
  calc x ≤ ↑⌈x⌉ := Int.le_ceil x
    _ ≤ (d : ℚ) := by exact_mod_cast (show ⌈x⌉ ≤ (d:ℤ) by omega)

private theorem le_floor_toNat_imp (x : ℚ) (d : Nat) (hx : 0 ≤ x) (h : d ≤ x.floor.toNat) :
    (d : ℚ) ≤ x := by
  change d ≤ ⌊x⌋.toNat at h
  have : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  calc (d : ℚ) ≤ ↑⌊x⌋ := by exact_mod_cast (show (d:ℤ) ≤ ⌊x⌋ by omega)
    _ ≤ x := Int.floor_le x

private theorem floor_toNat_succ_le_imp (x : ℚ) (d : Nat) (hx : 0 ≤ x)
    (h : x.floor.toNat + 1 ≤ d) : x < (d : ℚ) := by
  change ⌊x⌋.toNat + 1 ≤ d at h
  have : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  calc x < ↑⌊x⌋ + 1 := Int.lt_floor_add_one x
    _ ≤ (d : ℚ) := by exact_mod_cast (show ⌊x⌋ + 1 ≤ (d:ℤ) by omega)

private theorem le_ceil_sub_one_imp (x : ℚ) (d : Nat) (hx : 0 < x)
    (h : d ≤ (x.ceil - 1).toNat) : (d : ℚ) < x := by
  rw [rat_ceil_eq] at h
  have : 1 ≤ ⌈x⌉ := by exact_mod_cast Int.one_le_ceil_iff.mpr hx
  exact_mod_cast (Int.lt_ceil.mp (show (d:ℤ) < ⌈x⌉ by omega) : (↑d : ℚ) < x)

private theorem mkStripped_nonzero_iff (s : Bool) (d : Nat) (e : Int) :
    (mkStrippedDecimal s d e).digits ≠ 0 ↔ d ≠ 0 := by
  unfold mkStrippedDecimal; simp only []
  split
  · next h => simp [(strip_zero_iff d).mp h]
  · next h => exact Iff.intro (fun _ => mt (strip_zero_iff d).mpr h) (fun _ => h)

/-- If findDigits returns nonzero digits, |toRat| is in the interval [lo, hi]
    with strictness matching the interval's inclusivity flags. -/
theorem findDigits_in_interval (iv : AcceptanceInterval) (s : Bool)
    (lo hi : ℚ) (hlo : 0 ≤ lo) (hhi : 0 < hi) (n fuel : Nat) (hn : n ≥ 1) :
    (findDigits iv s lo hi n fuel).digits ≠ 0 →
    (if iv.lowInclusive then lo ≤ |(findDigits iv s lo hi n fuel).toRat|
     else lo < |(findDigits iv s lo hi n fuel).toRat|) ∧
    (if iv.highInclusive then |(findDigits iv s lo hi n fuel).toRat| ≤ hi
     else |(findDigits iv s lo hi n fuel).toRat| < hi) := by
  induction fuel generalizing n with
  | zero => unfold findDigits; simp
  | succ fuel' ih =>
    unfold findDigits; simp only []
    set scale := (10:ℚ)^(n-1) with hscale_def
    set dLow := (if iv.lowInclusive then (lo * scale).ceil.toNat
                 else (lo * scale).floor.toNat + 1)
    set dHigh := (if iv.highInclusive then (hi * scale).floor.toNat
                  else ((hi * scale).ceil - 1).toNat)
    by_cases hcond : dLow ≤ dHigh
    · rw [if_pos hcond]
      set d := max dLow (min ((lo + hi) / 2 * scale).floor.toNat dHigh)
      have hdl : dLow ≤ d := le_max_left _ _
      have hdh : d ≤ dHigh := max_le hcond (min_le_right _ _)
      intro hdigits
      have hd_ne : d ≠ 0 := (mkStripped_nonzero_iff s d _).mp hdigits
      have h_toRat := mkStripped_toRat s d (n - 1) hd_ne
      have hd_pos : (0:ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd_ne
      have hscale_pos : (0:ℚ) < scale := by positivity
      have h_abs : |(mkStrippedDecimal s d (-(n-1:Nat))).toRat| = (d : ℚ) / scale := by
        rw [h_toRat, abs_mul,
            show |(if s then (-1:ℚ) else 1)| = 1 from by cases s <;> simp,
            one_mul, abs_of_pos (div_pos hd_pos hscale_pos)]
      rw [h_abs]
      constructor
      · simp only [dLow] at hdl
        cases hli : iv.lowInclusive <;>
          simp only [hli, ↓reduceIte, Bool.false_eq_true] at hdl ⊢
        · rw [lt_div_iff₀ hscale_pos]
          exact floor_toNat_succ_le_imp _ _ (by positivity) hdl
        · rw [le_div_iff₀ hscale_pos]
          exact ceil_toNat_le_imp _ _ (by positivity) hdl
      · simp only [dHigh] at hdh
        cases hhi' : iv.highInclusive <;>
          simp only [hhi', ↓reduceIte, Bool.false_eq_true] at hdh ⊢
        · rw [div_lt_iff₀ hscale_pos]
          exact le_ceil_sub_one_imp _ _ (mul_pos hhi hscale_pos) hdh
        · rw [div_le_iff₀ hscale_pos]
          exact le_floor_toNat_imp _ _ (by positivity) hdh
    · rw [if_neg hcond]
      exact ih (n + 1) (by omega)

-- Sign lemmas
private theorem mkStripped_toRat_nonneg_false (d : Nat) (e : Int) :
    0 ≤ (mkStrippedDecimal false d e).toRat := by
  unfold mkStrippedDecimal; simp only []
  split
  · simp [Decimal.toRat]
  · next h =>
    unfold Decimal.toRat; simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    split
    · positivity
    · exact div_nonneg (by positivity) (by positivity)

private theorem mkStripped_toRat_nonpos_true (d : Nat) (e : Int) :
    (mkStrippedDecimal true d e).toRat ≤ 0 := by
  unfold mkStrippedDecimal; simp only []
  split
  · simp [Decimal.toRat]
  · next h =>
    unfold Decimal.toRat; simp only [↓reduceIte]
    have hsig : (0:ℚ) ≤ (stripTrailingZeros d).1 := by exact_mod_cast Nat.zero_le _
    split
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hsig) (by positivity)
    · exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hsig) (by positivity)

private theorem findDigits_toRat_nonneg_false (iv : AcceptanceInterval)
    (lo hi : ℚ) (n fuel : Nat) :
    0 ≤ (findDigits iv false lo hi n fuel).toRat := by
  induction fuel generalizing n with
  | zero => unfold findDigits; simp [Decimal.toRat]
  | succ fuel' ih =>
    unfold findDigits; simp only []
    by_cases hcond : (if iv.lowInclusive = true then (lo * 10 ^ (n - 1)).ceil.toNat
                      else (lo * 10 ^ (n - 1)).floor.toNat + 1) ≤
                     (if iv.highInclusive = true then (hi * 10 ^ (n - 1)).floor.toNat
                      else ((hi * 10 ^ (n - 1)).ceil - 1).toNat)
    · rw [if_pos hcond]; exact mkStripped_toRat_nonneg_false _ _
    · rw [if_neg hcond]; exact ih (n + 1)

private theorem findDigits_toRat_nonpos_true (iv : AcceptanceInterval)
    (lo hi : ℚ) (n fuel : Nat) :
    (findDigits iv true lo hi n fuel).toRat ≤ 0 := by
  induction fuel generalizing n with
  | zero => unfold findDigits; simp [Decimal.toRat]
  | succ fuel' ih =>
    unfold findDigits; simp only []
    by_cases hcond : (if iv.lowInclusive = true then (lo * 10 ^ (n - 1)).ceil.toNat
                      else (lo * 10 ^ (n - 1)).floor.toNat + 1) ≤
                     (if iv.highInclusive = true then (hi * 10 ^ (n - 1)).floor.toNat
                      else ((hi * 10 ^ (n - 1)).ceil - 1).toNat)
    · rw [if_pos hcond]; exact mkStripped_toRat_nonpos_true _ _
    · rw [if_neg hcond]; exact ih (n + 1)

-- Helpers for translating |toRat| bounds to contains
private theorem abs_bounds_to_contains_pos (iv : AcceptanceInterval) (r : ℚ)
    (hr_pos : 0 < r)
    (hlo : if iv.lowInclusive then iv.low ≤ |r| else iv.low < |r|)
    (hhi : if iv.highInclusive then |r| ≤ iv.high else |r| < iv.high) :
    iv.contains r := by
  rw [abs_of_pos hr_pos] at hlo hhi; exact ⟨hlo, hhi⟩

private theorem abs_bounds_to_contains_neg (iv : AcceptanceInterval) (r : ℚ)
    (hr_neg : r < 0) (absIv : AcceptanceInterval)
    (habsIv : absIv = { low := -iv.high, high := -iv.low,
                         lowInclusive := iv.highInclusive,
                         highInclusive := iv.lowInclusive })
    (hlo : if absIv.lowInclusive then absIv.low ≤ |r| else absIv.low < |r|)
    (hhi : if absIv.highInclusive then |r| ≤ absIv.high else |r| < absIv.high) :
    iv.contains r := by
  subst habsIv; rw [abs_of_neg hr_neg] at hlo hhi
  unfold AcceptanceInterval.contains; simp only [] at hlo hhi ⊢
  constructor
  · cases hli : iv.lowInclusive <;> cases hhi' : iv.highInclusive <;>
      simp only [hli, ↓reduceIte, Bool.false_eq_true] at hhi ⊢ <;> linarith
  · cases hli : iv.lowInclusive <;> cases hhi' : iv.highInclusive <;>
      simp only [hhi', ↓reduceIte, Bool.false_eq_true] at hlo ⊢ <;> linarith

/-- Fuel sufficiency: 1024 iterations is enough for findDigits to find a
    matching digit count for any finite non-zero F64. -/
axiom schubfach_fuel_sufficient (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    let iv := schubfachInterval x hfin
    let absIv := if x.sign then
      { low := -iv.high, high := -iv.low,
        lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive : AcceptanceInterval }
    else iv
    (findDigits absIv x.sign absIv.low absIv.high 1 1024).digits ≠ 0

/-- Compute the shortest decimal for a finite F64 (specification level).
    For negative x, the interval [low, high] has low ≤ high < 0,
    so |low| > |high|. We need sorted absolute bounds for findDigits,
    with correspondingly swapped inclusivity flags. -/
def shortestDecimal (x : F64) (hfin : x.isFinite) : Decimal :=
  let iv := schubfachInterval x hfin
  let s := x.sign
  if x.toRat = 0 then ⟨s, 0, 0⟩
  else
    let absIv : AcceptanceInterval :=
      if s then
        { low := -iv.high, high := -iv.low,
          lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive }
      else iv
    findDigits absIv s absIv.low absIv.high 1 1024

/-- The Ryu algorithm: F64 → shortest Decimal. -/
def ryu (x : F64) (hfin : x.isFinite) : Decimal :=
  shortestDecimal x hfin

/-- Ryu's output is in the acceptance interval (for non-zero x).
    Proved from findDigits_in_interval + sign analysis + fuel sufficiency. -/
theorem ryu_in_interval (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    isValidRep (ryu x hfin) x hfin := by
  unfold isValidRep ryu shortestDecimal
  rw [if_neg hne]; simp only []
  set iv := schubfachInterval x hfin
  cases hs : x.sign
  · -- s = false (positive): absIv = iv
    have hd : (findDigits iv false iv.low iv.high 1 1024).digits ≠ 0 := by
      have := schubfach_fuel_sufficient x hfin hne
      simp only [hs] at this; exact this
    have habs : 0 < iv.low ∧ iv.low < iv.high := by
      have := schubfach_abs_interval_pos x hfin hne
      simp only [hs] at this; exact this
    have ⟨hlo_bound, hhi_bound⟩ :=
      findDigits_in_interval iv false iv.low iv.high
        (le_of_lt habs.1) (lt_trans habs.1 habs.2) 1 1024 (by omega) hd
    have hnn := findDigits_toRat_nonneg_false iv iv.low iv.high 1 1024
    have habs_pos : 0 < |(findDigits iv false iv.low iv.high 1 1024).toRat| := by
      cases hli : iv.lowInclusive <;>
        simp only [hli, ↓reduceIte, Bool.false_eq_true] at hlo_bound
      · exact habs.1.trans hlo_bound
      · exact habs.1.trans_le hlo_bound
    exact abs_bounds_to_contains_pos iv _
      (by rwa [abs_of_nonneg hnn] at habs_pos) hlo_bound hhi_bound
  · -- s = true (negative): absIv is negated
    set negIv : AcceptanceInterval :=
      { low := -iv.high, high := -iv.low,
        lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive }
    have hd : (findDigits negIv true negIv.low negIv.high 1 1024).digits ≠ 0 := by
      have := schubfach_fuel_sufficient x hfin hne
      simp only [hs, ↓reduceIte] at this; exact this
    have habs : 0 < negIv.low ∧ negIv.low < negIv.high := by
      have := schubfach_abs_interval_pos x hfin hne
      simp only [hs, ↓reduceIte] at this; exact this
    have ⟨hlo_bound, hhi_bound⟩ :=
      findDigits_in_interval negIv true negIv.low negIv.high
        (le_of_lt habs.1) (lt_trans habs.1 habs.2) 1 1024 (by omega) hd
    have hnp := findDigits_toRat_nonpos_true negIv negIv.low negIv.high 1 1024
    have habs_pos : 0 < |(findDigits negIv true negIv.low negIv.high 1 1024).toRat| := by
      cases hli : negIv.lowInclusive <;>
        simp only [hli, ↓reduceIte, Bool.false_eq_true] at hlo_bound
      · exact habs.1.trans hlo_bound
      · exact habs.1.trans_le hlo_bound
    have hr_neg : (findDigits negIv true negIv.low negIv.high 1 1024).toRat < 0 := by
      rcases lt_or_eq_of_le hnp with h | h
      · exact h
      · exfalso; rw [h, abs_zero] at habs_pos; exact lt_irrefl _ habs_pos
    exact abs_bounds_to_contains_neg iv _ hr_neg negIv rfl hlo_bound hhi_bound

/-- Ryu produces well-formed Decimals. -/
theorem ryu_well_formed (x : F64) (hfin : x.isFinite) :
    (ryu x hfin).WellFormed := by
  unfold ryu shortestDecimal
  simp only []
  split
  · exact ⟨fun h => absurd rfl h, fun _ => rfl⟩
  · exact findDigits_well_formed _ _ _ _ _ _

private theorem digits_zero_imp_toRat_zero (d : Decimal) (h : d.digits = 0) :
    d.toRat = 0 := by
  unfold Decimal.toRat; simp [h]

private theorem round_zero : F64.roundToNearestEven 0 = F64.posZero := by
  unfold F64.roundToNearestEven; simp

private theorem posZero_toRat : F64.posZero.toRat = 0 := by
  unfold F64.posZero F64.toRat F64.isFinite F64.effectiveSignificand; simp

/-- For non-zero x, ryu produces non-zero digits.
    Proof: if digits were 0, then toRat = 0. Since ryu's output is in the
    acceptance interval, 0 would be in the interval. By interval soundness,
    roundToNearestEven 0 = x, but that gives posZero = x, contradicting x.toRat ≠ 0. -/
theorem ryu_nonzero_digits (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    (ryu x hfin).digits ≠ 0 := by
  intro h_zero
  have h_rat_zero := digits_zero_imp_toRat_zero _ h_zero
  have h_in := ryu_in_interval x hfin hne
  unfold isValidRep at h_in
  rw [h_rat_zero] at h_in
  have h_round := schubfach_interval_correct x hfin 0 h_in
  rw [round_zero] at h_round
  exact hne (by rw [← h_round]; exact posZero_toRat)

/-- effectiveSignificand = 0 iff the float is ±0. -/
private theorem effectiveSig_zero_iff (x : F64) (_hfin : x.isFinite) :
    x.effectiveSignificand = 0 ↔ (x.biasedExp.val = 0 ∧ x.mantissa.val = 0) := by
  unfold F64.effectiveSignificand
  constructor
  · intro h; split at h
    · exact ⟨‹_›, h⟩
    · simp [F64.mantBits] at h
  · intro ⟨he, hm⟩; simp [he, hm]

/-- toRat = 0 iff effectiveSignificand = 0 for finite floats.
    Proof: toRat = ±sig × 2^exp, where sig ≥ 0 and 2^exp > 0,
    so toRat = 0 ↔ sig = 0. -/
private theorem toRat_eq_zero_iff_sig_zero (x : F64) (hfin : x.isFinite) :
    x.toRat = 0 ↔ x.effectiveSignificand = 0 := by
  constructor
  · intro h0
    by_contra hsig
    have hsig_pos : (x.effectiveSignificand : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hsig
    have hsign : (if x.sign then (-1 : ℚ) else 1) ≠ 0 := by split <;> norm_num
    unfold F64.toRat at h0
    rw [if_neg (not_not.mpr hfin)] at h0
    simp only [] at h0
    split at h0
    · have h2 : (2 : ℚ) ^ x.effectiveBinaryExp.toNat ≠ 0 := by positivity
      exact absurd h0 (mul_ne_zero (mul_ne_zero hsign hsig_pos) h2)
    · have h2 : (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat ≠ 0 := by positivity
      rw [div_eq_zero_iff] at h0
      exact h0.elim (absurd · (mul_ne_zero hsign hsig_pos)) (absurd · h2)
  · intro hsig
    unfold F64.toRat
    rw [if_neg (not_not.mpr hfin)]
    simp [hsig]

/-- If a finite F64 has toRat = 0, it is ±0 (biasedExp = 0, mantissa = 0). -/
theorem toRat_zero_imp_zero (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0) :
    x.biasedExp.val = 0 ∧ x.mantissa.val = 0 :=
  (effectiveSig_zero_iff x hfin).mp ((toRat_eq_zero_iff_sig_zero x hfin).mp h0)

/-- The decimal-to-F64 roundtrip: toF64(ryu(x)) = x. -/
theorem ryu_roundtrip (x : F64) (hfin : x.isFinite) :
    (ryu x hfin).toF64 = x := by
  by_cases h0 : x.toRat = 0
  · -- x is ±0: ryu returns ⟨x.sign, 0, 0⟩
    have hryu : ryu x hfin = ⟨x.sign, 0, 0⟩ := by
      unfold ryu shortestDecimal; simp [h0]
    rw [hryu]
    simp [Decimal.toF64]
    -- Need: ⟨x.sign, ⟨0, _⟩, ⟨0, _⟩⟩ = x
    obtain ⟨he, hm⟩ := toRat_zero_imp_zero x hfin h0
    rcases x with ⟨s, ⟨e, he'⟩, ⟨m, hm'⟩⟩
    simp at he hm
    subst he; subst hm
    rfl
  · -- x is non-zero: ryu has non-zero digits, goes through roundToNearestEven
    have hd : (ryu x hfin).digits ≠ 0 := ryu_nonzero_digits x hfin h0
    simp [Decimal.toF64, hd]
    exact schubfach_interval_correct x hfin _ (ryu_in_interval x hfin h0)

end Ryu
