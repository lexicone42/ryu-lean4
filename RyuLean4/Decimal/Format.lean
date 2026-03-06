/-
  Decimal/Format.lean

  Format a Decimal to a string representation.
  Scientific notation: [-]<digit>[.<digits>]e<int>
-/
import RyuLean4.Decimal.Decimal

namespace Decimal

/-- Convert n > 0 to digit chars by prepending to acc (MSD first). -/
def natToDigitsAux (n : Nat) (acc : List Char) : List Char :=
  if n = 0 then acc
  else natToDigitsAux (n / 10) (Char.ofNat (n % 10 + 48) :: acc)
termination_by n

/-- Convert a Nat to its decimal digit characters. -/
def natToDigits (n : Nat) : List Char :=
  if n = 0 then ['0']
  else natToDigitsAux n []

/-- Convert an Int to decimal string chars (with optional minus). -/
def intToDigits (n : Int) : List Char :=
  match n with
  | .ofNat n => natToDigits n
  | .negSucc n => '-' :: natToDigits (n + 1)

/-- Format a Decimal to a string.
    Format: [-]<digit>[.<digits>]e<int> -/
def format (d : Decimal) : String :=
  let signChars := if d.sign then ['-'] else []
  if d.digits = 0 then
    String.ofList (signChars ++ ['0', 'e', '0'])
  else
    let allDigits := natToDigits d.digits
    let nDigits := allDigits.length
    let adjExp : Int := d.exponent + (nDigits - 1)
    let body :=
      match allDigits with
      | [c] => [c]
      | c :: rest => c :: '.' :: rest
      | [] => ['0']
    let expPart := 'e' :: intToDigits adjExp
    String.ofList (signChars ++ body ++ expPart)

end Decimal
