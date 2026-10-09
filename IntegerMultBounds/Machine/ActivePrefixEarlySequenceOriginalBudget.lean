import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalRun
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceBudget

/-! The original-input four-load machine retains the certified width exponent
while paying both header constructions, both cleanups and all four joins. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalBudget
open ActivePrefixEarlySequenceOriginalRun
open CompactGadgetReservationShape
open ActivePrefixLayoutShapes
open Networks

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (rows : ℕ),
    0<rows → 0<s.payload → (cost s p rows : ℝ)≤
      C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixEarlySequenceBudget.uniform_bound
  refine ⟨C+overhead+4,by positivity,?_⟩
  intro s p rows hr hp
  have hi := hbound s p rows hr hp
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have he : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(overhead : ℝ)+4 by positivity)
  unfold cost
  push_cast at hi hv hrest ⊢
  nlinarith only [hi,hv,hrest]

end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalBudget
