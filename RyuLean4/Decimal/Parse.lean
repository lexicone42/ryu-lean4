/-
  Decimal/Parse.lean

  Parse a string back to a Decimal.
  Must invert the format from Format.lean.
  Format: [-]<digit>[.<digits>]e<int>
-/
import RyuLean4.Decimal.Decimal

namespace Decimal

/-- Parse a single decimal digit character to its value. -/
def parseDigitChar (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else none

/-- Parse digits from a char list, accumulating the value. -/
def parseNatAux (chars : List Char) (acc : Nat) (consumed : Bool)
    : Option (Nat × List Char) :=
  match chars with
  | [] => if consumed then some (acc, []) else none
  | c :: rest =>
    match parseDigitChar c with
    | some d => parseNatAux rest (acc * 10 + d) true
    | none => if consumed then some (acc, c :: rest) else none

/-- Parse a sequence of digit chars to a natural number. -/
def parseNat (chars : List Char) : Option (Nat × List Char) :=
  parseNatAux chars 0 false

/-- Parse an integer (possibly negative). -/
def parseInt (chars : List Char) : Option (Int × List Char) :=
  match chars with
  | '-' :: rest =>
    match parseNat rest with
    | some (n, rest') => some (-(n : Int), rest')
    | none => none
  | _ =>
    match parseNat chars with
    | some (n, rest) => some (n, rest)
    | none => none

/-- Parse a formatted Decimal string back to a Decimal.
    Format: [-]<digit>[.<digits>]e<int> -/
def parse (s : String) : Option Decimal :=
  let chars := s.toList
  let (sign, chars) :=
    match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  match parseNat chars with
  | none => none
  | some (intPart, rest) =>
    let (fracDigits, numFracDigits, rest) :=
      match rest with
      | '.' :: rest' =>
        match parseNat rest' with
        | some (frac, rest'') =>
          let nFrac := rest'.length - rest''.length
          (frac, nFrac, rest'')
        | none => (0, 0, '.' :: rest')
      | _ => (0, 0, rest)
    match rest with
    | 'e' :: expChars =>
      match parseInt expChars with
      | some (exp, []) =>
        let fullDigits := intPart * 10^numFracDigits + fracDigits
        let fullExp := exp - numFracDigits
        some ⟨sign, fullDigits, fullExp⟩
      | _ => none
    | _ => none

end Decimal
