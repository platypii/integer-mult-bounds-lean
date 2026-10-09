import IntegerMultBounds.Machine.ActivePrefixCompactConjugationRun
import IntegerMultBounds.Machine.ActivePrefixCompactSwapBudget

/-! One uniform full-volume bound for both concrete compact conjugations,
including two interchanges, the actual load, and both sequential joins. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationBudget
open ActivePrefixCompactConjugationData ActivePrefixCompactConjugationRun
open CompactGadgetReservationShape
open Networks

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (kind : Kind) (s : Shape) (rows w : ℕ),
    0<rows → 0<s.payload → w≤s.H →
    (cost kind s rows w : ℝ)≤C*(rows*s.recordWidth : ℕ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixCompactSwapBudget.uniform_bound
  let L := ActivePrefixCompactParityLoad.constant+ActivePrefixCompactNegativeLoad.constant
  refine ⟨2*C+L+2,by positivity,?_⟩
  intro kind s rows w hr hp hw
  have hi := hbound s rows w hr hp hw
  have hl : constant kind≤L := by cases kind <;> dsimp only [constant,L] <;> omega
  have hl' : (constant kind : ℝ)≤(L : ℝ) := by exact_mod_cast hl
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have hpw : (1 : ℝ)≤((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 w) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hpw (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(L : ℝ)+2 by positivity)
  have hload := mul_le_mul_of_nonneg_right hl' (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  unfold cost
  rw [ActivePrefixCompactSwapData.volume_eq s rows w hw]
  push_cast at hi hv hrest hload ⊢
  nlinarith only [hi,hv,hrest,hload]

end IntegerMultBounds.Machine.ActivePrefixCompactConjugationBudget
