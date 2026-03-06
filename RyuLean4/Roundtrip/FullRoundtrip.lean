/-
  Roundtrip/FullRoundtrip.lean

  The complete roundtrip theorem:
    For all finite F64 values x:
      toF64(parse(format(ryu(x)))) = x

  Composes:
  1. ryu(x) → Decimal in acceptance interval
  2. format → string
  3. parse(format(...)) = ryu(x)  (format/parse roundtrip)
  4. toF64(ryu(x)) = x            (ryu_roundtrip)
-/
import RyuLean4.Ryu.ShortestRep
import RyuLean4.Roundtrip.FormatParse
import RyuLean4.Decimal.Format
import RyuLean4.Decimal.Parse

namespace Ryu

/-- The complete float-to-string-to-float roundtrip. -/
theorem full_roundtrip (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (ryu x hfin))).map Decimal.toF64 = some x := by
  rw [Decimal.format_parse_roundtrip _ (ryu_well_formed x hfin)]
  simp [Option.map]
  exact ryu_roundtrip x hfin

end Ryu
