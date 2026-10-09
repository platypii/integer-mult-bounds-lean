import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapRun

/-! Certified full-volume sublinear-width bound including physical descriptor
construction and cleanup around the complete binary interchange machine. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapBudget
open ActivePrefixDirtyControlUSwapData ActivePrefixDirtyControlUSwapRun
open CompactGadgetReservationShape
open Networks

 theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (rows w : ℕ),
    0<rows → 0<s.payload → w≤s.H →
    (cost s rows w : ℝ)≤C*(rows*s.recordWidth : ℕ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualShared.uniform_bound
  refine ⟨C+setupConstant+37,by positivity,?_⟩
  intro s rows w hr hp hw
  have hi := hbound (P s rows) (G s w) (B s w) w (headerWords s rows w)
    (by unfold P Shape.prefixRange; positivity) (by unfold G CompactGadgetReservationHeadersCarvedData.gap; positivity)
    (by unfold B CompactGadgetReservationHeadersCarvedData.suffix; positivity)
    (header_values s rows w) (header_canonical s rows w)
  change (BinaryRadixEqualShared.cost (P s rows) (G s w) (B s w) w (headerWords s rows w) : ℝ)≤
    C*(volume s rows w : ℝ)*((max 1 w : ℕ) : ℝ)^Parameters.tau at hi
  rw [volume_eq s rows w hw] at hi
  have hc := CompactGadgetReservationHeadersCarvedPlacedCleanup.carved_cost_bound s rows w .temp hr hp hw
  have hc' : (CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (headerWords s rows w) : ℝ)≤
      35*(rows*s.recordWidth : ℕ) := by exact_mod_cast hc
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have hpw : (1 : ℝ)≤((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 w) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hpw (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(setupConstant : ℝ)+37 by positivity)
  unfold cost
  push_cast at hi hc' hv hrest ⊢
  nlinarith only [hi,hc',hv,hrest]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapBudget
