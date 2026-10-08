import IntegerMultBounds.CostTable

/-! Reduction of the end-to-end theorem to a program with a cost function. A
program that halts with the correct product on every pair of `n`-bit inputs
within `total n` steps, where `total` is eventually a fixed multiple of the
target time, satisfies `Machine.ComputesWithin`; and `total` bounded by the
cost table of §8 is such a function. What remains for `Machine.EndToEnd` is
the program itself with its correctness and cost proofs. -/

namespace IntegerMultBounds.Assembly

open Filter Machine TimeBound CostTable

/-- A program halts correctly within `total n` steps on every `n`-bit pair. -/
def RunsWithin {t q a : ℕ} (M : Program t q a) (total : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (x y : List Bool), x.length = n → y.length = n →
    ∃ (k : ℕ) (c : Config t q a),
      run M k (input M x y) = some c ∧ step M c = none ∧
      outputCorrect M n x y c ∧ (k : ℝ) ≤ total n

/-- A cost function eventually a fixed multiple of the target time gives the
uniform eventual bound of `ComputesWithin`. -/
theorem computesWithin_of_runsWithin {t q a : ℕ} (M : Program t q a) (total : ℕ → ℝ) (κ : ℝ)
    (hrun : RunsWithin M total)
    (hbound : ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧ ∀ n, n₀ ≤ n → total n ≤ C * targetTime κ n) :
    ComputesWithin M κ := by
  obtain ⟨C, n₀, hC, hC'⟩ := hbound
  refine ⟨C, n₀, hC, ?_⟩
  intro n hn x y hx hy
  obtain ⟨k, c, hrun', hstep, hout, hk⟩ := hrun n hn x y hx hy
  exact ⟨k, c, hrun', hstep, hout, fun hn₀ => hk.trans (hC' n hn₀)⟩

/-- The end-to-end theorem follows from a program whose cost is bounded by the
cost table of §8: the volume times the seven rows, polynomial setup, and
bounded overheads. -/
theorem endToEnd_of_table (t q a : ℕ) (M : Program t q a) (total : ℕ → ℝ)
    (hrun : RunsWithin M total)
    (V : ℕ → ℝ) (cV : ℝ) (hV0 : ∀ n, 0 ≤ V n) (hV : ∀ n, V n ≤ cV * n)
    (setup : List (ℝ × ℝ)) (hsetup : ∀ s ∈ setup, 0 ≤ s.1 ∧ 0 ≤ s.2)
    (bounded : List (ℝ × (ℝ → ℝ) × ℝ))
    (hbounded : ∀ b ∈ bounded, 0 ≤ b.1 ∧ 0 ≤ b.2.2 ∧ ∀ᶠ p in atTop, b.2.1 p ≤ b.2.2)
    (htotal : ∀ᶠ n : ℕ in atTop, total n ≤ V n * tableRows n +
      (setup.map fun s => s.1 * precision n ^ s.2).sum +
      (bounded.map fun b => b.1 * V n * b.2.1 (precision n)).sum) :
    EndToEnd :=
  ⟨t, q, a, M, computesWithin_of_runsWithin M total _ hrun
    (table_time_bound V cV hV0 hV setup hsetup bounded hbounded total htotal)⟩

end IntegerMultBounds.Assembly
