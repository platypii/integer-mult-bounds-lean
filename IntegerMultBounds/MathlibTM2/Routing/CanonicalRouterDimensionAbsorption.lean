module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterDimension
public import IntegerMultBounds.MathlibTM2.Routing.SetupAbsorption

/-! The full dimension setup, repeated once per row, is eventually paid by
physical record volume. This does not discharge small dimensions or metadata input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open Filter
noncomputable section

/-- Complete repeated setup is eventually at most total routed volume,
uniformly in row count and positive payload width. -/
theorem canonicalPermutationDimensionBudget_eventually_le_volume :
    ∀ᶠ n : ℕ in atTop, ∀ R B : ℕ, 1 ≤ B →
      R * canonicalPermutationDimensionBudget n ≤ R * 2 ^ n * B :=
  repeatedPolynomialSetup_eventually_le_volume canonicalPermutationDimensionBudget
    canonicalPermutationDimensionCoefficient 7 canonicalPermutationDimensionBudget_polynomial

/-- The same absorption for the real-valued ledger used by execution prices. -/
theorem canonicalPermutationDimensionCost_eventually_le_volume :
    ∀ᶠ n : ℕ in atTop, ∀ R B : ℕ, 1 ≤ B →
      (R : ℝ) * canonicalPermutationDimensionCost n ≤ (R * 2 ^ n * B : ℕ) := by
  filter_upwards [canonicalPermutationDimensionBudget_eventually_le_volume] with n hn
  intro R B hB
  rw [canonicalPermutationDimensionCost_eq, ← Nat.cast_mul]
  exact Nat.cast_le.mpr (hn R B hB)

/-- A fixed dimension threshold; independent of row count and payload width. -/
def canonicalRouterDimensionThreshold : ℕ :=
  (Filter.eventually_atTop.mp canonicalPermutationDimensionBudget_eventually_le_volume).choose

theorem canonicalPermutationDimensionCost_le_volume (n R B : ℕ)
    (hn : canonicalRouterDimensionThreshold ≤ n) (hB : 1 ≤ B) :
    (R : ℝ) * canonicalPermutationDimensionCost n ≤ (R * 2 ^ n * B : ℕ) := by
  have h := (Filter.eventually_atTop.mp
    canonicalPermutationDimensionBudget_eventually_le_volume).choose_spec n hn R B hB
  rw [canonicalPermutationDimensionCost_eq, ← Nat.cast_mul]
  exact Nat.cast_le.mpr h

end
end IntegerMultBounds.MathlibTM2.Routing
