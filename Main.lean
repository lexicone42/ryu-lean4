import RyuLean4

open Ryu Decimal

/-- Construct a finite F64 with its finiteness proof. -/
private def mkFiniteF64 (sign : Bool) (bexp : Nat) (mant : Nat)
    (hbe : bexp < 2047 := by omega) (hm : mant < 2^52 := by omega) :
    { x : F64 // x.isFinite } :=
  let x : F64 := ⟨sign, ⟨bexp, by omega⟩, ⟨mant, hm⟩⟩
  ⟨x, F64.exp_lt_implies_finite x hbe⟩

/-- Show a test case: name, F64 fields, formatted output. -/
private def showCase (name : String) (sign : Bool) (bexp mant : Nat)
    (hbe : bexp < 2047 := by omega) (hm : mant < 2^52 := by omega) : IO Unit := do
  let ⟨x, hfin⟩ := mkFiniteF64 sign bexp mant hbe hm
  let d := ryu x hfin
  let s := Decimal.format d
  IO.println s!"  {name}: {s}  (digits={d.digits}, exp={d.exponent})"

def main : IO Unit := do
  IO.println "RyuLean4: Smoke tests"
  IO.println ""
  IO.println "Running ryu on concrete IEEE 754 doubles:"
  -- +0: sign=false, bexp=0, mant=0
  showCase "+0" false 0 0
  -- -0: sign=true, bexp=0, mant=0
  showCase "-0" true 0 0
  -- 1.0: sign=false, bexp=1023, mant=0
  -- value = 2^(1023-1023) × (1 + 0) = 1.0
  showCase "1.0" false 1023 0
  -- -1.0: sign=true, bexp=1023, mant=0
  showCase "-1.0" true 1023 0
  -- 2.0: sign=false, bexp=1024, mant=0
  showCase "2.0" false 1024 0
  -- 0.5: sign=false, bexp=1022, mant=0
  showCase "0.5" false 1022 0
  -- 0.1: sign=false, bexp=1019, mant=2702159776422298
  -- The nearest IEEE 754 double to 0.1
  showCase "≈0.1" false 1019 2702159776422298 (by omega) (by omega)
  -- Smallest positive subnormal: sign=false, bexp=0, mant=1
  -- value = 1 × 2^(-1074) ≈ 5 × 10^(-324)
  showCase "min subnormal" false 0 1
  -- Largest subnormal: sign=false, bexp=0, mant=2^52-1
  showCase "max subnormal" false 0 (2^52 - 1) (by omega) (by omega)
  -- Smallest positive normal: sign=false, bexp=1, mant=0
  -- value = 2^(-1022) ≈ 2.225 × 10^(-308)
  showCase "min normal" false 1 0
  -- Largest finite: sign=false, bexp=2046, mant=2^52-1
  showCase "max finite" false 2046 (2^52 - 1) (by omega) (by omega)
  IO.println ""
  IO.println "All cases computed successfully."
