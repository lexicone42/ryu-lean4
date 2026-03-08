# RyuLean4: Proof Narrative

A detailed walkthrough of how the complete float-to-string-to-float roundtrip is formally verified, from IEEE 754 bit-level representation through acceptance interval soundness.

## The theorem

```lean
theorem full_roundtrip (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (ryu x hfin))).map Decimal.toF64 = some x
```

This says: take any finite IEEE 754 double (including ±0, subnormals, and the full normal range), convert it to its shortest decimal string representation using the Ryu algorithm, parse that string back, and convert to F64 — you get the original value. No exceptions, no edge cases, no numerical precision caveats.

## Architecture: three independent stages

The proof decomposes the roundtrip into three stages, each verified independently:

```
           Stage 1                Stage 2              Stage 3
F64 ────────────→ Decimal ──────────→ String ──────────→ Decimal ──→ F64
    ryu(x,hfin)           format(d)          parse(s)        toF64(d)
```

- **Stage 1** (Ryu): `toF64(ryu(x)) = x` — the decimal-to-float roundtrip
- **Stage 2** (Format/Parse): `parse(format(d)) = some d` — string representation is lossless
- **Composition**: `full_roundtrip` chains all three in 5 lines

The key insight is that Stage 2 (string formatting) is *completely independent* of IEEE 754 — it's pure decimal-to-string reasoning. And Stage 1 doesn't care about strings at all. This separation makes the proofs manageable.

## The F64 model

### Bit-level representation

```lean
structure F64 where
  sign : Bool
  biasedExp : Fin 2048     -- 11-bit biased exponent
  mantissa : Fin (2^52)    -- 52-bit mantissa
```

Using `Fin` types enforces bit-width constraints at the type level. There's no possibility of constructing an invalid F64.

### Rational interpretation

Every finite F64 has an exact rational value:

```lean
def toRat (x : F64) : ℚ :=
  if ¬x.isFinite then 0
  else
    let s := if x.sign then -1 else 1
    let sig := (x.effectiveSignificand : ℚ)
    if x.effectiveBinaryExp ≥ 0 then
      s * sig * 2 ^ x.effectiveBinaryExp.toNat
    else
      s * sig / 2 ^ (-x.effectiveBinaryExp).toNat
```

The effective significand handles the normal/subnormal split:
- **Normal** (biasedExp ≥ 1): `2^52 + mantissa` (implicit leading 1)
- **Subnormal** (biasedExp = 0): `mantissa` (no implicit bit)

The effective binary exponent adjusts accordingly:
- **Normal**: `biasedExp - 1075` (includes the 52-bit mantissa shift)
- **Subnormal**: `-1074` (fixed)

All arithmetic in the formalization uses Mathlib's `ℚ`. There is no floating-point computation anywhere in the proofs.

## Stage 1: The Ryu algorithm

### The acceptance interval

The core idea of Ryu (and the earlier Schubfach algorithm): for a finite F64 `x`, there exists an interval of rationals that all round to `x` under round-to-nearest-even. Any decimal in this interval is a valid string representation.

```lean
def schubfachInterval (x : F64) (hfin : x.isFinite) : AcceptanceInterval :=
  let mf := x.effectiveSignificand
  let e2 := x.effectiveBinaryExp - 2
  let delta := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2
  let u := 4 * mf - delta      -- lower bound numerator
  let w := 4 * mf + 2          -- upper bound numerator
  -- Scale by 2^e2 and apply sign
  ...
```

The `u, w` bounds come from the Ryu paper (Section 2.2). The scaling by `4` (the `-2` in `e2 = ef - 2`) gives exactly one extra bit of precision needed for correct tie-breaking. The `delta` distinguishes exponent boundaries (`delta = 1` when the mantissa is zero and the exponent could decrease) from interior values (`delta = 2`).

Interval boundaries are inclusive when the mantissa is even (round-to-nearest-*even* ties to the current value) and exclusive when odd.

### Interval soundness: the hardest proof

```lean
theorem schubfach_interval_correct (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq : (schubfachInterval x hfin).contains q) :
    F64.roundToNearestEven q = x
```

This is the mathematical heart of the formalization — the claim that the Schubfach interval is *sound*. The proof was the last axiom eliminated and required ~1000 lines.

**Proof structure:**

1. **Sign analysis** (q ≠ 0, sign matches x): Since the interval for non-zero x doesn't contain 0, `q ≠ 0`. The sign of q matches x.sign because positive intervals have positive bounds and vice versa.

2. **Exponent recovery** (`findBiasedExp |q| = x.biasedExp`): This is the most complex subproof. `findBiasedExp` searches downward from 2046 for the correct biased exponent. The correctness proof (`findBiasedExp_correct`) establishes that `|x.toRat|` falls in the threshold interval `[threshQ(e), threshQ(e+1))` for `e = x.biasedExp`. Since q is in the acceptance interval around x, `|q|` falls in the same threshold interval, so `findBiasedExp` returns the same exponent.

   The threshold function:
   ```lean
   def threshQ (e : Nat) : ℚ :=
     if e ≥ 1023 then 2 ^ (e - 1023) else 1 / 2 ^ (1023 - e)
   ```

   Proving `|x.toRat| ∈ [threshQ(e), threshQ(e+1))` requires separate bounds for normal and subnormal floats, with careful handling of the effective significand range `[2^52, 2^53)` for normals.

3. **Significand recovery** (scaled q rounds to x's significand): With the exponent matched, the proof scales q by `2^(-binExp)` to get `sigExact ∈ [mf - 1/2, mf + 1/2]` where `mf` is x's effective significand. This scaling step requires proving bounds that translate between the `e2 = ef - 2` scaling of the acceptance interval and the `ef` scaling of the significand — the factor-of-4 cancellation `2^(ef-2) / 2^ef = 1/4` is mathematically trivial but requires careful case splitting on the sign of `ef`.

4. **Tie-breaking** (`round_in_half_interval`): The round-to-nearest-even rule at the half-integer boundaries `mf ± 1/2` connects to the interval's inclusivity flags. When `sigExact = mf - 1/2`:
   - If the mantissa is even, the interval includes this boundary, and round-to-even produces `mf` ✓
   - If the mantissa is odd, the interval *excludes* this boundary (strict inequality), so this case can't happen

   The proof for the odd case extracts a *strict* bound from the interval membership, which requires re-entering the `schubfachInterval` definition and showing that odd mantissa implies exclusive boundaries. This is where the `delta = 2` / mantissa parity connection is essential.

5. **Reconstruction** (`branchOf_mf`): With the correct significand recovered, the proof shows that the branch analysis in `roundSignificand` (handling subnormal→normal transitions, significand overflow) reproduces x's exact mantissa and biased exponent.

### Shortest decimal search

```lean
def findDigits (iv : AcceptanceInterval) (s : Bool)
    (absLow absHigh : ℚ) (n : Nat) (fuel : Nat) : Decimal
```

Starting at `n = 1` digit, the algorithm scales the interval to `[lo × 10^(n-1), hi × 10^(n-1)]`, computes the integer range `[dLow, dHigh]` via ceiling/floor, and checks if any integer falls in this range. If yes, it picks the center value and strips trailing zeros. If no, it increments `n`.

**Key theorems:**

- `findDigits_in_interval` — If findDigits returns non-zero digits, the result is in the interval (with correct strict/non-strict boundaries matching the interval's inclusivity flags).

- `findDigits_well_formed` — The result has no trailing zeros (ensured by `stripTrailingZeros`).

- `schubfach_fuel_sufficient` — 1024 iterations always suffice. The proof shows that `(hi - lo) × 10^359 ≥ 2` for all finite non-zero F64, which means by digit count 360, the scaled interval width is ≥ 2, guaranteeing at least one integer inside. The bound 359 comes from the minimum interval width (achieved at subnormal floats with `e2 = -1076`) and the relationship `10^359 ≥ 2^1077 > 2 × 2^1076`.

### Ryu roundtrip composition

```lean
theorem ryu_roundtrip (x : F64) (hfin : x.isFinite) :
    (ryu x hfin).toF64 = x
```

**Proof**: Split on whether x is zero. For ±0, `ryu` returns `⟨x.sign, 0, 0⟩` directly, and `toF64` reconstructs the zero. For non-zero x, `ryu_in_interval` shows the output is in the acceptance interval, then `schubfach_interval_correct` shows anything in the interval rounds back to x.

## Stage 2: Format/parse roundtrip

```lean
theorem format_parse_roundtrip (d : Decimal) (hwf : d.WellFormed) :
    parse (format d) = some d
```

This is proved independently of IEEE 754 — it's pure string manipulation.

### The 8-layer proof

The format function produces scientific notation: `[-]<digit>[.<digits>]e<int>`. The parse function is a hand-written recursive descent parser. The roundtrip proof inverts parsing through 8 layers:

**Layer 1** — Single digit characters. `parseDigitChar(Char.ofNat(d + 48)) = some d` for `d < 10`, plus non-digit classification (`'e'`, `'-'`, `'.'` all parse to `none`). Proved by `native_decide` after exhaustive case split.

**Layer 2** — Accumulator commutativity. `natToDigitsAux n acc = natToDigitsAux n [] ++ acc`. This establishes that the MSD-first digit generation is well-behaved with respect to appending.

**Layer 2b** — Structural properties. The digit list is non-empty for `n > 0`, never starts with minus, and every character is a digit. These guard against parser ambiguities.

**Layer 3** — Parser base case. `parseNatAux` terminates correctly when it encounters a non-digit character (returns accumulated value and remaining input).

**Layer 4** — Single digit parsing. `parseNatAux` correctly processes one digit character, updating the accumulator to `val * 10 + d`.

**Layer 5** — Full inversion. `parseNatAux(natToDigitsAux(n) ++ rest) = some (val * 10^len + n, rest)`. This is the core inductive step, proved by strong induction on `n`. The key arithmetic identity is `n = (n/10) * 10^(digits(n/10).length) + n%10`, validated by `Nat.div_add_mod` and `nlinarith`.

**Layer 6** — Natural number roundtrip. Lifts Layer 5 to `parseNat ∘ natToDigits`.

**Layer 7** — Integer roundtrip. Handles the optional minus sign for negative integers, using the structural property that digit strings never start with minus.

**Layer 7b** — Accumulator shifting for fractional parts. Generalizes the parsing of a sequence of digit characters with an arbitrary starting accumulator, needed for the fractional part after the decimal point.

**Layer 8** — Full roundtrip. Dispatches on the decimal structure:
- Zero digits: format produces `"0e0"`, parse recovers `⟨sign, 0, 0⟩`
- Single non-zero digit: format produces `<d>e<exp>`, no decimal point
- Multiple digits: format produces `<d1>.<rest>e<adjExp>`, with fractional parsing

Each case threads through the sign, integer part, optional fractional part, and exponent, applying the appropriate layer lemma at each step.

The proof operates on `List Char` rather than `String` (via `formatList`/`parseList` equivalences) to avoid the overhead of string manipulation lemmas.

## Stage 3: Composition

```lean
theorem full_roundtrip (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (ryu x hfin))).map Decimal.toF64 = some x := by
  rw [Decimal.format_parse_roundtrip _ (ryu_well_formed x hfin)]
  simp [Option.map]
  exact ryu_roundtrip x hfin
```

Five lines. Rewrite `parse(format(...))` to `some (ryu x hfin)` using Stage 2, simplify the `Option.map`, then apply Stage 1. The entire complexity is in the two sub-theorems.

## The axiom-reduction arc

The formalization was built incrementally, with axioms standing in for unproved theorems:

| Commit | Axioms | What was proved |
|--------|--------|-----------------|
| Initial skeleton | 4 | Basic structure, function definitions |
| `ryu_well_formed` | 4 | Output has no trailing zeros |
| `format_parse_roundtrip` | 4 | String roundtrip (independent of F64) |
| `findBiasedExp_correct` | 3 | Exponent recovery |
| `roundSignificand_exact` | 3 | Significand recovery |
| `ryu_nonzero_digits` | 2 | Non-zero input → non-zero output |
| `ryu_in_interval` | 2 | Output is in acceptance interval |
| `schubfach_abs_interval_pos` | 2 | Interval has positive bounds |
| `schubfach_fuel_sufficient` | 1 | 1024 iterations always suffice |
| `schubfach_interval_correct` | **0** | Acceptance interval soundness |

The last axiom was the hardest — it required the full rounding analysis with tie-breaking, sign handling, exponent recovery, and significand scaling. The proof is ~1000 lines and constitutes about 40% of the total formalization.

## Proof statistics

| Component | Lines | Key technique |
|-----------|-------|---------------|
| F64 model + classification | 174 | Dependent types (Fin), case analysis |
| Rational interpretation | 56 | Sign × significand × 2^exp decomposition |
| Round-to-nearest-even | 78 | Iterative search + floor/ceiling |
| Rounding correctness | 388 | Bounds reasoning, omega, floor/ceil |
| Acceptance intervals | 1106 | Scaling lemmas, tie-breaking analysis |
| Shortest decimal search | 684 | Fuel induction, interval width |
| Decimal model + format/parse | 175 | Recursive descent, accumulator |
| Format/parse roundtrip | 451 | 8-layer inversion |
| Full roundtrip | 28 | 5-line composition |
| **Total** | **~3140** | **Zero axioms, zero sorrys** |

## What's *not* proved

- **Shortest length**: `isShortestRep` is defined but not proved. The formalization guarantees the output is *valid* (in the interval) but doesn't prove no shorter representation exists. The algorithm clearly produces shortest output by construction (it tries 1 digit, then 2, then 3...), but formalizing this would require proving that no valid decimal with fewer digits exists, which needs a more detailed analysis of the digit ranges.

- **Performance**: The Lean implementation uses exact rational arithmetic and is not remotely competitive with C/Rust implementations. This is a specification, not an implementation.

- **Subnormal tie-breaking at zero**: The proof handles ±0 specially (ryu returns the trivial decimal). The interval analysis only applies to non-zero values.
