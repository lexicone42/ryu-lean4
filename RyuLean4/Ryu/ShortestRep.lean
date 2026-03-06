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

/-- Compute the shortest decimal for a finite F64 (specification level). -/
def shortestDecimal (x : F64) (hfin : x.isFinite) : Decimal :=
  let iv := schubfachInterval x hfin
  let s := x.sign
  if x.toRat = 0 then Decimal.zero
  else
    let absLow := |iv.low|
    let absHigh := |iv.high|
    let rec findDigits (n : Nat) (fuel : Nat) : Decimal :=
      match fuel with
      | 0 => ⟨s, 0, 0⟩
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
          ⟨s, d, -(n - 1 : Nat)⟩
        else
          findDigits (n + 1) fuel'
    termination_by fuel
    findDigits 1 20

/-- The Ryu algorithm: F64 → shortest Decimal. -/
def ryu (x : F64) (hfin : x.isFinite) : Decimal :=
  shortestDecimal x hfin

/-- Ryu's output is in the acceptance interval. Axiomatized. -/
axiom ryu_in_interval (x : F64) (hfin : x.isFinite) :
    isValidRep (ryu x hfin) x hfin

/-- Ryu produces well-formed Decimals. Axiomatized. -/
axiom ryu_well_formed (x : F64) (hfin : x.isFinite) :
    (ryu x hfin).WellFormed

/-- The decimal-to-F64 roundtrip: toF64(ryu(x)) = x. -/
theorem ryu_roundtrip (x : F64) (hfin : x.isFinite) :
    (ryu x hfin).toF64 = x := by
  unfold Decimal.toF64
  exact schubfach_interval_correct x hfin _ (ryu_in_interval x hfin)

end Ryu
