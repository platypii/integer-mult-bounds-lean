import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationRun
import IntegerMultBounds.Machine.ActivePrefixCompactSwapBudget
import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapBudget

/-! Uniform full-volume sublinear-width bound for every concrete compact
conjugation, including both swaps and the complete original-input load. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationBudget
open ActivePrefixDirtyControlConjugationData ActivePrefixDirtyControlConjugationRun
open CompactGadgetReservationShape
open Networks

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (kind : Kind) (s : Shape) (rows w : ℕ),
    0<rows → 0<s.payload → w≤s.H →
    (cost kind s rows w : ℝ)≤C*(rows*s.recordWidth : ℕ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨CT,hCT,ht⟩ := ActivePrefixCompactSwapBudget.uniform_bound
  obtain ⟨CU,hCU,hu⟩ := ActivePrefixDirtyControlUSwapBudget.uniform_bound
  let L := ActivePrefixDirtyControlLoad.constant+ActivePrefixDirtyControlNegativePureLoad.constant
  refine ⟨2*(CT+CU)+L+2,by dsimp [L]; positivity,?_⟩
  intro kind s rows w hr hp hw
  have hswap : (swapCost kind s rows w : ℝ)≤(CT+CU)*(rows*s.recordWidth : ℕ)*((max 1 w : ℕ) : ℝ)^Parameters.tau := by
    have hT := ht s rows w hr hp hw
    have hU := hu s rows w hr hp hw
    have hV : (0 : ℝ)≤(rows*s.recordWidth : ℕ) := by positivity
    have hpow : (0 : ℝ)≤((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.rpow_nonneg (by positivity) _
    cases kind <;> dsimp [swapCost]
    all_goals nlinarith only [hT,hU,mul_nonneg hV hpow,mul_nonneg hCT.le (mul_nonneg hV hpow),
      mul_nonneg hCU.le (mul_nonneg hV hpow)]
  have hl : loadConstant kind≤L := by cases kind <;> dsimp [loadConstant,L] <;> omega
  have hV : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have hpw : (1 : ℝ)≤((max 1 w : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 w) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hpw (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(L : ℝ)+2 by positivity)
  have hl' : (loadConstant kind : ℝ)≤L := by exact_mod_cast hl
  unfold cost
  push_cast at hrest hl' hswap hV ⊢
  nlinarith only [hswap,hV,hrest,mul_le_mul_of_nonneg_right hl' (show (0 : ℝ)≤(rows : ℝ)*s.recordWidth by positivity)]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationBudget
