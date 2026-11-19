module

import IntegerMultBounds.MathlibTM2.Fast.CompactFinalR
public import IntegerMultBounds.MathlibTM2.Statement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Integer multiplication below `n log n` on Mathlib's Turing machines

`mulInTime` exposes the explicit improved saving; `statement` retains the existential
interface in `Statement.lean`. Both follow from the rounded compact host multiplier
`compactR_mulInTime_final` and its checked runtime bound at `ε = 31/64`.

The exact-arithmetic chains (`mulInTime_exact`, `compact_mulInTime` and the `d^6 ≤ b` width
lemmas behind them) no longer hold above `ε = 1/4` and were removed; restore them from the parent
of the commit that introduced this note.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2

/-- The complete compact multiplier has the explicit saving `4223103985 · 2^-46`, the layer margin
`ε (1-λ')` rounded down, with `ε = 31/64` and `1-λ' = 12389970 · 10^-11` just below
`1-τ = 123899714039 · 10^-15`, about `2^-14.02`. -/
theorem mulInTime : MulInTime (4223103985 / 2 ^ 46 : ℝ) :=
  Fast.Main.compactR_mulInTime_final

/-- The saving exceeds `10 · 2^-33`. -/
theorem saving_gt : 10 * (2 ^ 33 : ℝ)⁻¹ < 4223103985 / 2 ^ 46 := by norm_num

theorem statement : Statement :=
  ⟨_, by positivity, mulInTime⟩

end IntegerMultBounds.MathlibTM2
