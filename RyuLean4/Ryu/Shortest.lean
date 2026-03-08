/-
  Ryu/Shortest.lean

  Proof that ryu produces a scale-minimal decimal representation.
  The Ryu algorithm's output is found at the earliest scale (step number)
  where an integer fits in the acceptance interval.
-/
import RyuLean4.Ryu.ShortestRep
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 800000

namespace Ryu

/-! ## Core lemma: findDigits returns at the first successful scale -/

/-- findDigits returns at some step n₀, and all earlier steps have no valid integer.
    This is the key structural property: findDigits tries steps in order and only
    recurses past step k when no integer fits at that scale. -/
theorem findDigits_step_info (iv : AcceptanceInterval) (s : Bool)
    (n fuel : Nat)
    (hd : (findDigits iv s iv.low iv.high n fuel).digits ≠ 0) :
    ∃ n₀, n₀ ≥ n ∧ n₀ < n + fuel ∧
      (∀ k, n ≤ k → k < n₀ → noIntegerAtScale iv k) ∧
      ¬noIntegerAtScale iv n₀ := by
  induction fuel generalizing n with
  | zero => unfold findDigits at hd; simp at hd
  | succ fuel' ih =>
    -- Decide whether step n succeeds or fails
    by_cases hn : noIntegerAtScale iv n
    · -- Step n fails (no integer at this scale), findDigits recurses
      -- Show findDigits takes the else branch
      have hd' : (findDigits iv s iv.low iv.high (n + 1) fuel').digits ≠ 0 := by
        unfold noIntegerAtScale at hn
        unfold findDigits at hd
        simp only [] at hd hn
        rwa [if_neg hn] at hd
      obtain ⟨n₀, hn₀_ge, hn₀_lt, hprior, hsuccess⟩ := ih (n + 1) hd'
      exact ⟨n₀, by omega, by omega,
        fun k hge hlt => by
          rcases eq_or_lt_of_le hge with rfl | hgt
          · exact hn
          · exact hprior k (by omega) hlt,
        hsuccess⟩
    · -- Step n succeeds (an integer exists at this scale)
      exact ⟨n, le_refl n, by omega,
        fun _ hge hlt => absurd hlt (Nat.not_lt.mpr hge),
        hn⟩

/-! ## Main theorem: ryu is scale-minimal -/

/-- The ryu algorithm produces a scale-minimal representation.
    For zero floats, it outputs ±0. For non-zero floats, it finds the
    coarsest grid resolution where an integer fits in the acceptance interval. -/
theorem ryu_shortest (x : F64) (hfin : x.isFinite) :
    isShortestRep (ryu x hfin) x hfin := by
  unfold isShortestRep
  constructor
  · -- Zero case: ryu returns ⟨x.sign, 0, 0⟩
    intro h0
    unfold ryu shortestDecimal
    simp [h0]
  · -- Non-zero case
    intro hne
    constructor
    · exact ryu_in_interval x hfin hne
    · -- Scale-minimality from findDigits_step_info
      -- Show ryu x hfin = findDigits (absInterval x hfin) ...
      have hryu_eq : ryu x hfin = findDigits (absInterval x hfin) x.sign
          (absInterval x hfin).low (absInterval x hfin).high 1 1024 := by
        unfold ryu shortestDecimal absInterval
        simp [hne]
      have hd := ryu_nonzero_digits x hfin hne
      rw [hryu_eq] at hd
      obtain ⟨n₀, hn₀_ge, _, hprior, hsuccess⟩ :=
        findDigits_step_info (absInterval x hfin) x.sign 1 1024 hd
      exact ⟨n₀, hn₀_ge, hprior, hsuccess⟩

end Ryu
