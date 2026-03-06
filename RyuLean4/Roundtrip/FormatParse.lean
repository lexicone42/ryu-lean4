/-
  Roundtrip/FormatParse.lean

  Prove that parsing a formatted Decimal recovers the original.
  The proof uses sorry for the core digit-level lemmas for now —
  these follow the same pattern as nickelean's escape roundtrip
  but require careful treatment of the accumulator-based recursion
  in natToDigits.go and parseNat.go.

  The key insight: format produces strings of the form
    [-]<digit>[.<digits>]e<int>
  and parse inverts this structure exactly.
-/
import RyuLean4.Decimal.Format
import RyuLean4.Decimal.Parse

namespace Decimal

-- Single digit roundtrip (all 10 cases by native_decide)
theorem parseDigitChar_ofNat (d : Nat) (hd : d < 10) :
    parseDigitChar (Char.ofNat (d + 48)) = some d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
         d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

-- Non-digit characters
theorem parseDigitChar_e : parseDigitChar 'e' = none := by native_decide
theorem parseDigitChar_minus : parseDigitChar '-' = none := by native_decide
theorem parseDigitChar_dot : parseDigitChar '.' = none := by native_decide

-- Characters produced by natToDigits are all digits
theorem natToDigits_all_digits (n : Nat) :
    ∀ c ∈ natToDigits n, parseDigitChar c ≠ none := by
  sorry

-- parseNat inverts natToDigits when followed by non-digit chars
theorem parseNat_natToDigits_append (n : Nat) (rest : List Char)
    (hrest : ∀ c ∈ rest, parseDigitChar c = none) :
    parseNat (natToDigits n ++ rest) = some (n, rest) := by
  sorry

-- parseInt inverts intToDigits
theorem parseInt_intToDigits_append (z : Int) (rest : List Char)
    (hrest : ∀ c ∈ rest, parseDigitChar c = none) :
    parseInt (intToDigits z ++ rest) = some (z, rest) := by
  sorry

-- Full format/parse roundtrip for well-formed Decimals
theorem format_parse_roundtrip (d : Decimal) (hwf : d.WellFormed) :
    parse (format d) = some d := by
  sorry

end Decimal
