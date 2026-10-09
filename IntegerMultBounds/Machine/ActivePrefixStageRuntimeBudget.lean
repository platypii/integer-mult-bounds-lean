import IntegerMultBounds.Machine.ActivePrefixStageRuntimeRun
import IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatchBudget

/-! Both physical runtime selectors and all singleton work are absorbed by
the certified packed exponent, uniformly in the original stage width. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeData

theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hp : 1<d.stage.f → Packed d D),
      (cost D d hp : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨P,hP,hpacked⟩ := ActivePrefixStageDispatchBudget.uniform_bound D
  obtain ⟨S,hS,hsingle⟩ := ActivePrefixStageSingletonDispatchBudget.uniform_bound
  refine ⟨P+S+43,by positivity,?_⟩
  intro s d hp
  have ho : (ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f) : ℝ)+4≤
      43*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast ActivePrefixStageWidthOriginal.overhead_bound d
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hov := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤43*(d.rows*s.recordWidth : ℕ) by positivity)
  by_cases h : 1<d.stage.f
  · have hb := hpacked s d (by omega) (hp h).guard
    have hs : 0≤S*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by positivity
    rw [cost,dite_eq_left h]
    push_cast at ho hov hb hs ⊢
    nlinarith only [ho,hov,hb,hs]
  · have hb := hsingle (singleton d h)
    have hs := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤S*(d.rows*s.recordWidth : ℕ) by positivity)
    have hpos : 0≤P*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by positivity
    change (ActivePrefixStageSingletonDispatch.cost (singleton d h) : ℝ)≤S*(d.rows*s.recordWidth : ℕ) at hb
    rw [cost,dite_eq_right h]
    push_cast at ho hov hb hs hpos ⊢
    nlinarith only [ho,hov,hb,hs,hpos]

end IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget
