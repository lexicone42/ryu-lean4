/-
  Roundtrip/FormatParse.lean

  Prove that parsing a formatted Decimal recovers the original.
  Axiomatized for now — proof follows nickelean's escape roundtrip pattern.
-/
import RyuLean4.Decimal.Format
import RyuLean4.Decimal.Parse

namespace Decimal

/-- Format then parse roundtrip for well-formed Decimals. -/
axiom format_parse_roundtrip (d : Decimal) (hwf : d.WellFormed) :
    parse (format d) = some d

end Decimal
