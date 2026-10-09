import IntegerMultBounds.Machine.ActivePrefixStageDispatchRun
import IntegerMultBounds.Machine.ActivePrefixStageFullBudget

/-! Reading source order and clearing its flag preserve the certified compact
exponent. Only the actually selected original-input stage is charged. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageDispatchRun

theorem overhead {s : Shape} (d : Inputs s) :
    ActivePrefixStageOrderCompare.cost d.stage+4≤27*(d.rows*s.recordWidth) := by
  have h := ActivePrefixStageOrderCompare.cost_linear d.stage d.rows d.hG d.hGK d.hr d.hrecord
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hv : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  omega

theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard),
      (cost D d hn hb : ℝ)≤C*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨E,hE,early⟩ := ActivePrefixStageFullBudget.early_uniform_bound D
  obtain ⟨L,hL,late⟩ := ActivePrefixStageFullBudget.late_uniform_bound D
  refine ⟨E+L+27,by positivity,?_⟩
  intro s d hn hb
  have ho : (ActivePrefixStageOrderCompare.cost d.stage : ℝ)+4≤27*(d.rows*s.recordWidth : ℕ) := by
    exact_mod_cast overhead d
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hp := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤27*(d.rows*s.recordWidth : ℕ) by positivity)
  by_cases h : d.stage.source.val<d.stage.target.val
  · have hb := early s d h
    have hl : 0≤L*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by positivity
    rw [cost,dite_eq_left h]
    push_cast at hb ho hp hl ⊢
    nlinarith only [hb,ho,hp,hl]
  · have hb := late s d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) hn hb
    have hl : 0≤E*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by positivity
    rw [cost,dite_eq_right h]
    push_cast at hb ho hp hl ⊢
    nlinarith only [hb,ho,hp,hl]

end IntegerMultBounds.Machine.ActivePrefixStageDispatchBudget
