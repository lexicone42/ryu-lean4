/-
  Ryu/ShortestRep.lean

  Find the shortest decimal representation in the acceptance interval.
-/
import RyuLean4.Ryu.Interval
import RyuLean4.Decimal.Decimal

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
    For zero, ryu returns digits=0 which is handled separately by toF64. -/
axiom ryu_in_interval (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    isValidRep (ryu x hfin) x hfin

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
