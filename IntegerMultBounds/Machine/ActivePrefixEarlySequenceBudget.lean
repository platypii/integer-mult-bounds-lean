import IntegerMultBounds.Machine.ActivePrefixEarlySequenceRun

/-! Certified width-exponent cost for the actual four-call shared schedule.
Every producer, repeated offset, swap, rotation, cleanup and join is charged. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceBudget
open CompactGadgetReservationShape
open ActivePrefixLayoutShapes
open Networks

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (rows : ℕ),
    0<rows → 0<s.payload →
    (ActivePrefixEarlySequenceRun.cost s p rows : ℝ)≤
      C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixCompactConjugationBudget.uniform_bound
  let L := ActivePrefixSelectedLoad.constant+ActivePrefixCorrectionLoad.constant
  refine ⟨2*C+L+3,by positivity,?_⟩
  intro s p rows hr hp
  have hpar := hbound .parity s rows (p.n*p.b) hr hp p.compactFits
  have hneg := hbound .negative s rows (p.n*p.b) hr hp p.compactFits
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have hpw : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hpw
    (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(L : ℝ)+3 by positivity)
  unfold ActivePrefixEarlySequenceRun.cost
  dsimp only [L] at hrest ⊢
  push_cast at hpar hneg hv hrest ⊢
  nlinarith only [hpar,hneg,hv,hrest]
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceBudget
