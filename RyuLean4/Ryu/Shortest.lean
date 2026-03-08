/-
  Ryu/Shortest.lean

  Infrastructure for proving that ryu produces the shortest decimal representation.
  This file is NOT imported by the main build — it contains work-in-progress
  toward the isShortestRep property.

  Key insight: isValidRep uses interval containment, not roundtrip correctness.
  So we don't need interval completeness — just that if findDigits fails at
  step k (dLow > dHigh), then no k-digit decimal has toRat in the interval.
-/
import RyuLean4.Ryu.ShortestRep
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 800000

namespace Ryu

/-! ## countDigits characterization -/

/-- numDigits is always ≥ 1. -/
theorem numDigits_pos (d : Decimal) : d.numDigits ≥ 1 := by
  unfold Decimal.numDigits Decimal.countDigits
  split
  · exact le_refl 1
  · omega

/-- For non-zero digits, 10^(numDigits-1) ≤ digits < 10^numDigits. -/
theorem numDigits_bounds (n : Nat) (hn : n > 0) :
    10 ^ (Decimal.countDigits n - 1) ≤ n ∧ n < 10 ^ Decimal.countDigits n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold Decimal.countDigits
    split
    · next hlt => exact ⟨by omega, by omega⟩
    · next hge =>
      push_neg at hge
      have hdiv_pos : n / 10 > 0 := Nat.div_pos hge (by omega)
      have hdiv_lt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have ⟨hlo, hhi⟩ := ih (n / 10) hdiv_lt hdiv_pos
      set cd := Decimal.countDigits (n / 10) with hcd_def
      have hcd_pos : cd ≥ 1 := by
        unfold Decimal.countDigits at hcd_def; split at hcd_def <;> omega
      constructor
      · -- 10^cd ≤ n
        show 10 ^ (1 + cd - 1) ≤ n
        rw [show 1 + cd - 1 = cd from by omega]
        have : 10 ^ cd ≤ 10 * (n / 10) := by
          have : 10 * 10 ^ (cd - 1) = 10 ^ cd := by
            conv_rhs => rw [show cd = (cd - 1) + 1 from by omega]
            simp [Nat.pow_succ, Nat.mul_comm]
          linarith [Nat.mul_le_mul_left 10 hlo]
        linarith [Nat.mul_div_le n 10]
      · -- n < 10^(cd+1)
        show n < 10 ^ (1 + cd)
        rw [show 1 + cd = cd + 1 from by omega]
        have : 10 * (n / 10 + 1) ≤ 10 * 10 ^ cd := Nat.mul_le_mul_left 10 hhi
        have : n < 10 * (n / 10 + 1) := by omega
        calc n < 10 * (n / 10 + 1) := by omega
          _ ≤ 10 * 10 ^ cd := Nat.mul_le_mul_left 10 hhi
          _ = 10 ^ (cd + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-! ## Status: Work in Progress

The remaining infrastructure needed for the full `isShortestRep` proof:

1. `findDigits_fail_no_integer`: If findDigits fails at step k (dLow > dHigh),
   no integer m satisfies both interval bounds at scale 10^(k-1).
   Requires floor/ceil ↔ Nat reasoning with non-negativity hypotheses.

2. `decimal_in_interval_gives_integer`: Any Decimal d' with |d'.toRat| in [lo,hi]
   and numDigits d' = k implies existence of integer m < 10^k at step k.
   Requires relating Decimal.toRat to the scaled integer view.

3. `findDigits_minimality`: Combining the above via induction on the steps
   findDigits skips.

4. `ryu_shortest`: Final composition: ryu_in_interval + findDigits_minimality
   = isShortestRep.

The proven lemma above (numDigits_bounds) provides the digit-counting foundation.
-/

end Ryu
