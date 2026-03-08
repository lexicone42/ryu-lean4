# RyuLean4

Formal verification of the [Ryu](https://dl.acm.org/doi/10.1145/3296979.3192369) float-to-string algorithm in Lean 4, proving the complete roundtrip property for IEEE 754 double-precision floats.

**Main theorem**: For all finite `F64` values `x`:

```lean
theorem full_roundtrip (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (ryu x hfin))).map Decimal.toF64 = some x
```

Converting a float to a decimal string and parsing it back yields the original float — proved for all ~2^63 finite IEEE 754 doubles, with zero axioms and zero `sorry`s.

## What this proves

The Ryu algorithm (Ulf Adams, PLDI 2018) converts IEEE 754 floats to their shortest decimal representation. This library formalizes the complete pipeline:

1. **Acceptance interval soundness** (`schubfach_interval_correct`) — Any rational in the Schubfach interval `[u·2^e₂, w·2^e₂]` rounds back to the original float under round-to-nearest-even.

2. **Ryu produces valid output** (`ryu_in_interval`) — The shortest-representation search always finds a decimal within the acceptance interval.

3. **Round-to-nearest-even is an involution** (`round_nearest_nonzero`) — `roundToNearestEven(toRat(x)) = x` for all finite non-zero F64.

4. **Format/parse roundtrip** (`format_parse_roundtrip`) — Scientific notation formatting and parsing are exact inverses for well-formed decimals.

5. **Fuel sufficiency** (`schubfach_fuel_sufficient`) — 1024 iterations is always enough to find a matching digit count, proved via interval width analysis (width × 10^359 ≥ 2).

## Project structure

```
RyuLean4/
├── IEEE754/
│   ├── Float64.lean            # F64 structure (sign, biasedExp, mantissa)
│   ├── Classify.lean           # Float classification (zero/subnormal/normal/inf/NaN)
│   ├── Value.lean              # F64 → ℚ rational interpretation
│   ├── RoundToNearest.lean     # ℚ → F64 rounding (round-to-nearest-even)
│   └── RoundProof.lean         # Correctness: RNE(toRat(x)) = x
├── Ryu/
│   ├── Interval.lean           # Schubfach acceptance intervals + soundness proof
│   └── ShortestRep.lean        # Shortest decimal search + termination proof
├── Decimal/
│   ├── Decimal.lean            # Decimal floating-point model
│   ├── Format.lean             # Decimal → scientific notation string
│   └── Parse.lean              # String → Decimal parser
└── Roundtrip/
    ├── FormatParse.lean        # 8-layer format/parse roundtrip proof
    └── FullRoundtrip.lean      # Composition of all three stages
```

## Building

Requires [Lean 4](https://lean-lang.org/) v4.29.0-rc4 (see `lean-toolchain`) and [Mathlib4](https://github.com/leanprover-community/mathlib4).

```bash
lake build
```

First build fetches Mathlib (~20 min). Subsequent builds are incremental.

## Proof architecture

The formalization decomposes the roundtrip into three independently verified stages:

```
F64 ──ryu──→ Decimal ──format──→ String ──parse──→ Decimal ──toF64──→ F64
      │                                                          │
      └──── ryu_roundtrip: toF64(ryu(x)) = x ──────────────────┘
                    format_parse_roundtrip: parse(format(d)) = d
```

Each stage has its own correctness theorem. The full roundtrip (`FullRoundtrip.lean`) is a 5-line composition.

## Key proof techniques

- **Rational arithmetic throughout** — All computation uses Mathlib's `ℚ`, avoiding any floating-point operations in proofs.
- **Fuel-based termination** — `findDigits` uses bounded iteration (1024 steps), with a separate proof that fuel always suffices.
- **Interval width analysis** — Proves `(hi - lo) × 10^359 ≥ 2` for all finite F64, guaranteeing a valid digit count exists within 360 iterations.
- **Tie-breaking case analysis** — Round-to-nearest-even requires careful handling at half-integer boundaries, connecting mantissa parity to interval inclusivity.
- **8-layer parser inversion** — `FormatParse.lean` builds the format/parse roundtrip from individual digit, number, sign, and exponent lemmas.

## Axiom status

**Zero axioms. Zero sorrys.** All proofs are constructive and fully checked by Lean's kernel.

The formalization went through an axiom-reduction arc:
- 4 axioms → 3 → 2 → 1 → **0** across multiple sessions
- Final axiom eliminated: `schubfach_interval_correct` (acceptance interval soundness)

## Known limitations

- **Shortestness not proven** — `isShortestRep` is defined in `ShortestRep.lean` but no theorem connects it to `ryu`'s output. The algorithm tries digit counts in ascending order so it should find the shortest, but minimality is not formally established. The roundtrip guarantee is complete regardless.
- **F64 is a mathematical model** — The `F64` structure is a pure Lean type, not connected to Lean's native `Float` or any hardware implementation. The proof applies to the model, which faithfully mirrors the IEEE 754 binary64 specification.
- **6 `native_decide` uses** — All on concrete character comparisons (digits 0-9, sign characters) in `FormatParse.lean`. These are sound but trust the Lean compiler for evaluation.

## Related work

- [nickelean](https://github.com/lexicone42/nickelean) — Formally verified JSON roundtrip for Nickel values in Lean 4.
- [Ryu paper](https://dl.acm.org/doi/10.1145/3296979.3192369) — Ulf Adams, "Ryū: fast float-to-string conversion", PLDI 2018.

## License

MIT
