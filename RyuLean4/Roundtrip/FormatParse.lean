/-
  Roundtrip/FormatParse.lean

  Prove: parse(format(d)) = some d for well-formed Decimals.
-/
import RyuLean4.Decimal.Format
import RyuLean4.Decimal.Parse
import Mathlib.Tactic.NormNum

namespace Decimal

/-! ## Layer 1: Single digit -/

theorem parseDigitChar_ofNat (d : Nat) (hd : d < 10) :
    parseDigitChar (Char.ofNat (d + 48)) = some d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
         d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

theorem parseDigitChar_e : parseDigitChar 'e' = none := by native_decide
theorem parseDigitChar_minus : parseDigitChar '-' = none := by native_decide
theorem parseDigitChar_dot : parseDigitChar '.' = none := by native_decide

theorem digit_char_ne_minus (d : Nat) (hd : d < 10) :
    Char.ofNat (d + 48) ≠ '-' := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
         d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

/-! ## Layer 2: natToDigitsAux accumulator spec -/

theorem natToDigitsAux_acc (n : Nat) (acc : List Char) :
    natToDigitsAux n acc = natToDigitsAux n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [natToDigitsAux]
    · have h1 : natToDigitsAux n acc =
          natToDigitsAux (n / 10) (Char.ofNat (n % 10 + 48) :: acc) := by
        rw [natToDigitsAux]; simp [hn]
      have h2 : natToDigitsAux n [] =
          natToDigitsAux (n / 10) [Char.ofNat (n % 10 + 48)] := by
        rw [natToDigitsAux]; simp [hn]
      rw [h1, h2]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
          (Char.ofNat (n % 10 + 48) :: acc)]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
          [Char.ofNat (n % 10 + 48)]]
      simp [List.append_assoc]

/-! ## Layer 2b: natToDigitsAux properties -/

theorem natToDigitsAux_ne_nil (n : Nat) (hn : n > 0) :
    natToDigitsAux n [] ≠ [] := by
  rw [natToDigitsAux]; simp [show ¬(n = 0) by omega]
  rw [natToDigitsAux_acc]; simp

theorem natToDigitsAux_mem (n : Nat) (c : Char) (hc : c ∈ natToDigitsAux n []) :
    ∃ d, d < 10 ∧ c = Char.ofNat (d + 48) := by
  induction n using Nat.strongRecOn generalizing c with
  | _ n ih =>
    rw [natToDigitsAux] at hc
    split at hc
    · simp at hc
    · next hn =>
      rw [natToDigitsAux_acc] at hc
      simp at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) c hc
      · exact ⟨n % 10, by omega, hc⟩

theorem natToDigits_ne_nil (n : Nat) : natToDigits n ≠ [] := by
  simp [natToDigits]; split
  · simp
  · exact natToDigitsAux_ne_nil n (by omega)

theorem natToDigits_not_starts_minus (n : Nat) (cs : List Char) :
    ∀ r, natToDigits n ++ cs ≠ '-' :: r := by
  intro r h
  have hne := natToDigits_ne_nil n
  obtain ⟨c, tail, hct⟩ := List.exists_cons_of_ne_nil hne
  rw [hct, List.cons_append] at h
  have hceq : c = '-' := List.head_eq_of_cons_eq h
  subst hceq
  simp [natToDigits] at hct
  split at hct
  · simp at hct
  · next hn =>
    have hcmem : '-' ∈ natToDigitsAux n [] := by rw [hct]; simp
    obtain ⟨d, hd, hcd⟩ := natToDigitsAux_mem n '-' hcmem
    exact absurd hcd.symm (digit_char_ne_minus d hd)

/-! ## Layer 3: parseNatAux helpers -/

theorem parseNatAux_rest (val : Nat) (rest : List Char)
    (hrest : rest = [] ∨ (∃ c cs, rest = c :: cs ∧ parseDigitChar c = none)) :
    parseNatAux rest val true = some (val, rest) := by
  rcases hrest with rfl | ⟨c, cs, rfl, hc⟩
  · simp [parseNatAux]
  · simp [parseNatAux, hc]

/-! ## Layer 4: parseNatAux on a digit (any consumed flag) -/

theorem parseNatAux_digit (d : Nat) (hd : d < 10) (rest : List Char)
    (val : Nat) (b : Bool) :
    parseNatAux (Char.ofNat (d + 48) :: rest) val b
    = parseNatAux rest (val * 10 + d) true := by
  cases b <;> simp [parseNatAux, parseDigitChar_ofNat d hd]

/-! ## Layer 5: parseNatAux inverts natToDigitsAux -/

theorem parseNatAux_natToDigitsAux (n : Nat) (hn : n > 0)
    (rest : List Char) (val : Nat) (b : Bool) :
    parseNatAux (natToDigitsAux n [] ++ rest) val b
    = parseNatAux rest (val * (10 ^ (natToDigitsAux n []).length) + n) true := by
  induction n using Nat.strongRecOn generalizing val b rest with
  | _ n ih =>
    by_cases hn10 : n / 10 = 0
    · -- Single digit case: n < 10
      have hlt : n < 10 := by
        by_contra h; push_neg at h
        have := Nat.div_pos h (by omega); omega
      have hunfold : natToDigitsAux n [] = [Char.ofNat (n % 10 + 48)] := by
        rw [natToDigitsAux]; simp [show ¬(n = 0) by omega, hn10, natToDigitsAux]
      rw [hunfold]; simp
      rw [parseNatAux_digit (n % 10) (by omega) rest val b]
      congr 1; simp [Nat.mod_eq_of_lt hlt]
    · -- Multi-digit case
      have hndiv : n / 10 > 0 := by omega
      have hunfold : natToDigitsAux n [] =
          natToDigitsAux (n / 10) [] ++ [Char.ofNat (n % 10 + 48)] := by
        conv_lhs => rw [natToDigitsAux]; simp [show ¬(n = 0) by omega]
        rw [natToDigitsAux_acc]
      rw [hunfold, List.append_assoc, List.singleton_append]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) hndiv
          (Char.ofNat (n % 10 + 48) :: rest) val b]
      rw [parseNatAux_digit (n % 10) (by omega) rest _ true]
      congr 1
      simp [List.length_append]
      have hdm := Nat.div_add_mod n 10
      rw [Nat.pow_succ]
      nlinarith

/-! ## Layer 6: parseNat inverts natToDigits -/

theorem parseNat_natToDigits_append (n : Nat) (rest : List Char)
    (hrest : rest = [] ∨ (∃ c cs, rest = c :: cs ∧ parseDigitChar c = none)) :
    parseNat (natToDigits n ++ rest) = some (n, rest) := by
  simp only [parseNat, natToDigits]
  split
  · -- n = 0
    next h =>
    subst h
    simp only [List.singleton_append]
    rw [show ('0' : Char) = Char.ofNat (0 + 48) from rfl]
    rw [parseNatAux_digit 0 (by omega) rest 0 false]
    simp
    exact parseNatAux_rest 0 rest hrest
  · -- n > 0
    next hn =>
    rw [parseNatAux_natToDigitsAux n (by omega) rest 0 false]
    simp
    exact parseNatAux_rest n rest hrest

/-! ## Layer 7: parseInt inverts intToDigits -/

theorem parseInt_intToDigits_append (z : Int) (rest : List Char)
    (hrest : rest = [] ∨ (∃ c cs, rest = c :: cs ∧ parseDigitChar c = none)) :
    parseInt (intToDigits z ++ rest) = some (z, rest) := by
  cases z with
  | ofNat n =>
    simp only [intToDigits]
    unfold parseInt
    split
    · next r heq =>
      exfalso; exact natToDigits_not_starts_minus n rest r heq
    · simp [parseNat_natToDigits_append n rest hrest]
  | negSucc n =>
    simp only [intToDigits, List.cons_append]
    unfold parseInt
    simp only
    rw [parseNat_natToDigits_append (n + 1) rest hrest]
    simp; omega

/-! ## Layer 7b: parseNatAux accumulator shift for digit chars -/

theorem parseNatAux_acc_shift (chars rest : List Char) (acc : Nat)
    (hall : ∀ c ∈ chars, ∃ d, d < 10 ∧ c = Char.ofNat (d + 48))
    (hrest : rest = [] ∨ (∃ c cs, rest = c :: cs ∧ parseDigitChar c = none)) :
    ∃ v, parseNatAux (chars ++ rest) 0 true = some (v, rest) ∧
         parseNatAux (chars ++ rest) acc true = some (acc * 10 ^ chars.length + v, rest) := by
  induction chars generalizing acc with
  | nil =>
    refine ⟨0, ?_, ?_⟩ <;> simp <;> exact parseNatAux_rest _ rest hrest
  | cons c cs ih =>
    obtain ⟨d, hd, hcd⟩ := hall c (by simp)
    subst hcd
    have hall' : ∀ c ∈ cs, ∃ d, d < 10 ∧ c = Char.ofNat (d + 48) :=
      fun c hc => hall c (List.mem_cons_of_mem _ hc)
    simp only [List.cons_append]
    rw [parseNatAux_digit d hd (cs ++ rest) 0 true]
    rw [parseNatAux_digit d hd (cs ++ rest) acc true]
    simp only [Nat.zero_mul, Nat.zero_add]
    obtain ⟨v', hv0, hvd⟩ := ih d hall'
    obtain ⟨v'', hv0', hvacc⟩ := ih (acc * 10 + d) hall'
    have hveq : v' = v'' := by
      have h := hv0.symm.trans hv0'
      cases h; rfl
    subst hveq
    refine ⟨d * 10 ^ cs.length + v', hvd, ?_⟩
    rw [hvacc]
    congr 1
    simp [List.length_cons, Nat.pow_succ]
    ring

/-! ## Layer 8: Full format/parse roundtrip -/

/-- List-level version of format (avoids String roundtrip in proofs). -/
private def formatList (d : Decimal) : List Char :=
  let signChars := if d.sign then ['-'] else []
  if d.digits = 0 then
    signChars ++ ['0', 'e', '0']
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
    signChars ++ body ++ expPart

/-- List-level version of parse (avoids String roundtrip in proofs). -/
private def parseList (chars : List Char) : Option Decimal :=
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

private theorem format_eq_ofList (d : Decimal) :
    format d = String.ofList (formatList d) := by
  simp only [format, formatList]
  split <;> rfl

private theorem parse_ofList_eq (l : List Char) :
    parse (String.ofList l) = parseList l := by
  unfold parse parseList
  simp only [String.toList_ofList]
  rfl

/-- Sign detection: parseList on a list starting with '-' -/
private theorem parseList_minus (rest : List Char) :
    parseList ('-' :: rest) =
    match parseNat rest with
    | none => none
    | some (intPart, rest') =>
      let (fracDigits, numFracDigits, rest') :=
        match rest' with
        | '.' :: rest'' =>
          match parseNat rest'' with
          | some (frac, rest''') => (frac, rest''.length - rest'''.length, rest''')
          | none => (0, 0, '.' :: rest'')
        | _ => (0, 0, rest')
      match rest' with
      | 'e' :: expChars =>
        match parseInt expChars with
        | some (exp, []) =>
          some ⟨true, intPart * 10^numFracDigits + fracDigits, exp - numFracDigits⟩
        | _ => none
      | _ => none := by
  unfold parseList; rfl

/-- Sign detection: parseList on a list not starting with '-' -/
private theorem parseList_not_minus (c : Char) (rest : List Char) (hc : c ≠ '-') :
    parseList (c :: rest) =
    match parseNat (c :: rest) with
    | none => none
    | some (intPart, rest') =>
      let (fracDigits, numFracDigits, rest') :=
        match rest' with
        | '.' :: rest'' =>
          match parseNat rest'' with
          | some (frac, rest''') => (frac, rest''.length - rest'''.length, rest''')
          | none => (0, 0, '.' :: rest'')
        | _ => (0, 0, rest')
      match rest' with
      | 'e' :: expChars =>
        match parseInt expChars with
        | some (exp, []) =>
          some ⟨false, intPart * 10^numFracDigits + fracDigits, exp - numFracDigits⟩
        | _ => none
      | _ => none := by
  unfold parseList; simp [hc]

theorem format_parse_roundtrip (d : Decimal) (hwf : d.WellFormed) :
    parse (format d) = some d := by
  rw [format_eq_ofList, parse_ofList_eq]
  rcases d with ⟨sign, digits, exponent⟩
  obtain ⟨hwf_trail, hwf_exp⟩ := hwf
  by_cases hd0 : digits = 0
  · subst hd0
    have := hwf_exp rfl; subst this
    cases sign <;> native_decide
  · -- digits > 0: setup
    set allDigits := natToDigits digits with h_ad
    have had_ne : allDigits ≠ [] := h_ad ▸ natToDigits_ne_nil digits
    have had_eq : allDigits = natToDigitsAux digits [] := by
      simp [natToDigits, hd0, h_ad]
    have had_mem : ∀ c ∈ allDigits, ∃ d, d < 10 ∧ c = Char.ofNat (d + 48) := by
      intro c hc; rw [had_eq] at hc; exact natToDigitsAux_mem digits c hc
    obtain ⟨c, rest_digits, hcr⟩ := List.exists_cons_of_ne_nil had_ne
    have hc_digit := had_mem c (by rw [hcr]; simp)
    obtain ⟨d1, hd1_lt, hd1_eq⟩ := hc_digit
    subst hd1_eq
    cases rest_digits with
    | nil =>
      -- Single digit: natToDigits digits = [Char.ofNat (d1 + 48)]
      have hnd : natToDigits digits = [Char.ofNat (d1 + 48)] := by rw [← h_ad, hcr]
      have hadjExp : exponent + (↑(natToDigits digits).length - 1 : Int) = exponent := by
        rw [hnd]; simp
      cases sign
      · -- sign = false, single digit
        have hfmt : formatList ⟨false, digits, exponent⟩ =
            Char.ofNat (d1 + 48) :: 'e' :: intToDigits exponent := by
          simp only [formatList, if_neg hd0, hnd]; simp
        rw [hfmt, parseList_not_minus _ _ (digit_char_ne_minus d1 hd1_lt)]
        rw [show Char.ofNat (d1 + 48) :: 'e' :: intToDigits exponent =
            natToDigits digits ++ ('e' :: intToDigits exponent) from by rw [hnd]; simp]
        rw [parseNat_natToDigits_append digits _
            (Or.inr ⟨'e', _, rfl, parseDigitChar_e⟩)]
        show (match parseInt (intToDigits exponent) with
          | some (exp, []) =>
            some (Decimal.mk false (digits * 10 ^ 0 + 0) (exp - ↑0))
          | _ => none) = some (Decimal.mk false digits exponent)
        rw [show intToDigits exponent = intToDigits exponent ++ [] from by simp]
        rw [parseInt_intToDigits_append exponent [] (Or.inl rfl)]; simp
      · -- sign = true, single digit
        have hfmt : formatList ⟨true, digits, exponent⟩ =
            '-' :: Char.ofNat (d1 + 48) :: 'e' :: intToDigits exponent := by
          simp only [formatList, if_neg hd0, hnd]; simp
        rw [hfmt, parseList_minus]
        rw [show Char.ofNat (d1 + 48) :: 'e' :: intToDigits exponent =
            natToDigits digits ++ ('e' :: intToDigits exponent) from by rw [hnd]; simp]
        rw [parseNat_natToDigits_append digits _
            (Or.inr ⟨'e', _, rfl, parseDigitChar_e⟩)]
        show (match parseInt (intToDigits exponent) with
          | some (exp, []) =>
            some (Decimal.mk true (digits * 10 ^ 0 + 0) (exp - ↑0))
          | _ => none) = some (Decimal.mk true digits exponent)
        rw [show intToDigits exponent = intToDigits exponent ++ [] from by simp]
        rw [parseInt_intToDigits_append exponent [] (Or.inl rfl)]; simp
    | cons c2 rest_digits' =>
      -- Multi digit: natToDigits digits = Char.ofNat (d1+48) :: c2 :: rest_digits'
      have hnd : natToDigits digits = Char.ofNat (d1 + 48) :: c2 :: rest_digits' := by
        rw [← h_ad, hcr]
      set tail := c2 :: rest_digits' with h_tail
      have htail_mem : ∀ ch ∈ tail, ∃ d, d < 10 ∧ ch = Char.ofNat (d + 48) :=
        fun ch hch => had_mem ch (by rw [hcr]; exact List.mem_cons_of_mem _ hch)
      have hlen : allDigits.length = tail.length + 1 := by rw [hcr]; simp
      set adjExp := exponent + ↑tail.length with h_adjExp
      set eRest := 'e' :: intToDigits adjExp
      have hrest_e' : eRest = [] ∨ (∃ c cs, eRest = c :: cs ∧ parseDigitChar c = none) :=
        Or.inr ⟨'e', _, rfl, parseDigitChar_e⟩
      -- Get fracVal from parseNatAux_acc_shift
      obtain ⟨fracVal, hfrac0, hfracd1⟩ :=
        parseNatAux_acc_shift tail eRest d1 htail_mem hrest_e'
      -- Derive d1 * 10^tail.length + fracVal = digits
      have hparse_full := parseNat_natToDigits_append digits eRest hrest_e'
      rw [hnd, List.cons_append] at hparse_full
      simp only [parseNat] at hparse_full
      rw [parseNatAux_digit d1 hd1_lt (tail ++ eRest) 0 false] at hparse_full
      simp only [Nat.zero_mul, Nat.zero_add] at hparse_full
      have hdigits_eq : d1 * 10 ^ tail.length + fracVal = digits := by
        have := hparse_full.symm.trans hfracd1; cases this; rfl
      -- parseNat (tail ++ eRest) = some (fracVal, eRest)
      have hc2_digit := htail_mem c2 (by simp [h_tail])
      obtain ⟨d2, hd2_lt, hd2_eq⟩ := hc2_digit
      have hparseNat_tail : parseNat (tail ++ eRest) = some (fracVal, eRest) := by
        show parseNatAux (tail ++ eRest) 0 false = some (fracVal, eRest)
        rw [h_tail, List.cons_append, hd2_eq, parseNatAux_digit d2 hd2_lt]
        simp only [Nat.zero_mul, Nat.zero_add]
        have : parseNatAux (tail ++ eRest) 0 true
            = parseNatAux (rest_digits' ++ eRest) d2 true := by
          rw [h_tail, List.cons_append, hd2_eq, parseNatAux_digit d2 hd2_lt]
          simp only [Nat.zero_mul, Nat.zero_add]
        rw [← this]; exact hfrac0
      have h_expEq : adjExp - ↑tail.length = exponent := by rw [h_adjExp]; omega
      cases sign
      · -- sign = false, multi digit
        have hfmt : formatList ⟨false, digits, exponent⟩ =
            Char.ofNat (d1 + 48) :: '.' :: (tail ++ eRest) := by
          simp only [formatList, if_neg hd0, hnd]
          simp [List.cons_append]; rfl
        rw [hfmt, parseList_not_minus _ _ (digit_char_ne_minus d1 hd1_lt)]
        simp only [parseNat, parseNatAux_digit d1 hd1_lt, Nat.zero_mul, Nat.zero_add,
          parseNatAux_rest d1 _ (Or.inr ⟨'.', _, rfl, parseDigitChar_dot⟩)]
        rw [show parseNatAux (tail ++ eRest) 0 false =
            parseNat (tail ++ eRest) from rfl, hparseNat_tail]
        show (match parseInt (intToDigits adjExp) with
          | some (exp, []) =>
            some (Decimal.mk false
              (d1 * 10 ^ ((tail ++ eRest).length - eRest.length) + fracVal)
              (exp - ↑((tail ++ eRest).length - eRest.length)))
          | _ => none) = some (Decimal.mk false digits exponent)
        rw [show intToDigits adjExp = intToDigits adjExp ++ [] from by simp]
        rw [parseInt_intToDigits_append adjExp [] (Or.inl rfl)]
        simp only [List.length_append, Nat.add_sub_cancel, hdigits_eq, h_expEq]
      · -- sign = true, multi digit
        have hfmt : formatList ⟨true, digits, exponent⟩ =
            '-' :: Char.ofNat (d1 + 48) :: '.' :: (tail ++ eRest) := by
          simp only [formatList, if_neg hd0, hnd]
          simp [List.cons_append]; rfl
        rw [hfmt, parseList_minus]
        simp only [parseNat, parseNatAux_digit d1 hd1_lt, Nat.zero_mul, Nat.zero_add,
          parseNatAux_rest d1 _ (Or.inr ⟨'.', _, rfl, parseDigitChar_dot⟩)]
        rw [show parseNatAux (tail ++ eRest) 0 false =
            parseNat (tail ++ eRest) from rfl, hparseNat_tail]
        show (match parseInt (intToDigits adjExp) with
          | some (exp, []) =>
            some (Decimal.mk true
              (d1 * 10 ^ ((tail ++ eRest).length - eRest.length) + fracVal)
              (exp - ↑((tail ++ eRest).length - eRest.length)))
          | _ => none) = some (Decimal.mk true digits exponent)
        rw [show intToDigits adjExp = intToDigits adjExp ++ [] from by simp]
        rw [parseInt_intToDigits_append adjExp [] (Or.inl rfl)]
        simp only [List.length_append, Nat.add_sub_cancel, hdigits_eq, h_expEq]

end Decimal
