import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceRun

/-! End-to-end cost of the prepared later-source schedule, including its
twelve compact swaps, ten full rotations, generated streams and all cleanup. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceBudget
open ActivePrefixDirtyControlSequenceData ActivePrefixDirtyControlSequenceStages ActivePrefixDirtyControlSequenceRun
open CompactGadgetReservationShape
open Networks

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (g : Geometry s),
    (cost s g : ℝ)≤C*(g.rows*s.recordWidth : ℕ)*((max 1 (g.n*g.b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixDirtyControlConjugationBudget.uniform_bound
  refine ⟨6*C+4*ActivePrefixDirtyControlLoad.constant+9,by positivity,?_⟩
  intro s g
  have hP := hbound .tPure s g.rows (g.n*g.b) g.positiveRows g.positivePayload g.compactFits
  have hN := hbound .tNegative s g.rows (g.n*g.b) g.positiveRows g.positivePayload g.compactFits
  have hL := hbound .uPure s g.rows (g.n*g.b) g.positiveRows g.positivePayload g.compactFits
  have hU := hbound .uNegative s g.rows (g.n*g.b) g.positiveRows g.positivePayload g.compactFits
  have hV : (1 : ℝ)≤(g.rows*s.recordWidth : ℕ) := by
    have h : 0<g.rows*s.recordWidth := by have := g.positiveRows; have := g.positivePayload; unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have hpw : (1 : ℝ)≤((max 1 (g.n*g.b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (g.n*g.b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hpw (show (0 : ℝ)≤(g.rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm
    (show (0 : ℝ)≤4*(ActivePrefixDirtyControlLoad.constant : ℝ)+9 by positivity)
  unfold cost earlyCost targetCost pureCost negativeCost loadCost unloadCost
  push_cast at hV hrest hP hN hL hU ⊢
  nlinarith only [hP,hN,hL,hU,hrest,hV]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceBudget
