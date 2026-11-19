module

public import IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Layer.SelectedMoments

/-- At exponent one the selected bit profile can pay at most 35 additional unit-rank
children per invocation across the nine stages and 32 replicas. -/
theorem bit_extra_rank_budget (k : ℕ) :
    (bitHistogram.map (fun e => e.1 * e.2)).sum + 9 * 32 * k < 64 * 28416 ↔ k ≤ 35 := by
  change 1808352 + 288 * k < 1818624 ↔ k ≤ 35
  omega

end IntegerMultBounds.MathlibTM2.M6
