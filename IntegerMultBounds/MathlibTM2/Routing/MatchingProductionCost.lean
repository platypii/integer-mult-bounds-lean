module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFullProfileProduction

/-! A uniform quadratic-in-width setup bound for actual full-table profile
production, including all traversal counts, copies and temporary-table erasure. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem matchingFullProfileProductionCost_eq (p : Par) (L Lk Lc : ℕ) :
    matchingFullProfileProductionCost p L Lk Lc =
      (p.n * p.K) * (12 * L * Lk + 105 * L + 30 * Lk + 8 * Lc * L + 8 * Lc + 136) +
        p.n * (38 * L + 58) + 11 * Lc + 34 := by
  unfold matchingFullProfileProductionCost matchingProfileProductionCost binaryPrefixExtractCost residueDispatchCost
  ring

theorem matchingFullProfileProductionCost_le (p : Par) (L Lk Lc s : ℕ)
    (hL : L ≤ s) (hLk : Lk ≤ s) (hLc : Lc ≤ s) :
    matchingFullProfileProductionCost p L Lk Lc ≤ 160 * (p.n * p.K + p.n + 1) * (s + 1) ^ 2 := by
  have hmain : 12 * L * Lk + 105 * L + 30 * Lk + 8 * Lc * L + 8 * Lc + 136 ≤
      160 * (s + 1) ^ 2 := by
    calc
      _ ≤ 12 * s * s + 105 * s + 30 * s + 8 * s * s + 8 * s + 136 := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (s : ℤ)]
  have hcount : 38 * L + 58 ≤ 160 * (s + 1) ^ 2 := by nlinarith
  have hconstant : 11 * Lc + 34 ≤ 160 * (s + 1) ^ 2 := by nlinarith
  rw [matchingFullProfileProductionCost_eq]
  calc
    _ ≤ (p.n * p.K) * (160 * (s + 1) ^ 2) + p.n * (160 * (s + 1) ^ 2) +
        160 * (s + 1) ^ 2 := by
      have h₁ := Nat.mul_le_mul_left (p.n * p.K) hmain
      have h₂ := Nat.mul_le_mul_left p.n hcount
      omega
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Routing
