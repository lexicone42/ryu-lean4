/-
  Decimal/Format.lean

  Format a Decimal to a string representation.
  We use scientific notation-style: optional sign, digits with decimal point,
  optional exponent. But for simplicity and to match common float formatting,
  we use a format like: [-]d.ddd[eN]

  For the Ryu algorithm, the output format is typically:
    [-]d.ddddEe  (scientific notation)
  or fixed notation for values in a reasonable range.

  We use a simplified format that's easy to prove roundtrips:
    The digits are written with a decimal point after the first digit,
    followed by an 'e' and the adjusted exponent.

  Example: Decimal.mk false 314 (-2) → "3.14e0" or "3.14"
-/
import RyuLean4.Decimal.Decimal

namespace Decimal

/-- Convert a Nat to its decimal digit characters. -/
def natToDigits (n : Nat) : List Char :=
  if n = 0 then ['0']
  else
    let rec go (n : Nat) (acc : List Char) : List Char :=
      if n = 0 then acc
      else go (n / 10) (Char.ofNat (n % 10 + 48) :: acc)
    termination_by n
    go n []

/-- Convert an Int to decimal string chars (with optional minus). -/
def intToDigits (n : Int) : List Char :=
  match n with
  | .ofNat n => natToDigits n
  | .negSucc n => '-' :: natToDigits (n + 1)

/-- Format a Decimal to a string.

    Format: [-]<digits>e<exponent>
    where digits has a decimal point after the first digit if there
    are multiple digits.

    Examples:
      Decimal(false, 314, -2)  → "3.14e0"
      Decimal(false, 1, 5)     → "1e5"
      Decimal(true, 25, -1)    → "-2.5e0"
      Decimal(false, 0, 0)     → "0e0"
-/
def format (d : Decimal) : String :=
  let signChars := if d.sign && d.digits ≠ 0 then ['-'] else []
  if d.digits = 0 then
    String.ofList (signChars ++ ['0', 'e', '0'])
  else
    let allDigits := natToDigits d.digits
    let nDigits := allDigits.length
    -- Adjusted exponent: the exponent as if we wrote d.ddd × 10^adj
    let adjExp : Int := d.exponent + (nDigits - 1)
    let body :=
      match allDigits with
      | [c] => [c]
      | c :: rest => c :: '.' :: rest
      | [] => ['0']  -- shouldn't happen
    let expPart := 'e' :: intToDigits adjExp
    String.ofList (signChars ++ body ++ expPart)

end Decimal
