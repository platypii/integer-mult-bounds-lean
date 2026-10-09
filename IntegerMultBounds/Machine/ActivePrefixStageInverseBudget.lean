import IntegerMultBounds.Machine.ActivePrefixStageDispatchInverseRun

/-! A reverse stage has the forward cost. Paying two complete runs and their
join also preserves the same uniform compact-width exponent. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageInverseBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)

def scale {s : Shape} (d : Inputs s) : ℝ :=
  (d.rows*s.recordWidth : ℕ)*((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau

theorem one_le_scale {s : Shape} (d : Inputs s) : 1≤scale d := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hv0 : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; have := d.hr; positivity
  have hv : 1≤d.rows*s.recordWidth := hv0
  have he : (1 : ℝ)≤((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hv' : (1 : ℝ)≤(d.rows*s.recordWidth : ℕ) := by exact_mod_cast hv
  exact one_le_mul_of_one_le_of_one_le hv' he

theorem twice_bound {s : Shape} (d : Inputs s) (B : ℕ) (C : ℝ)
    (h : (B : ℝ)≤C*scale d) : ((2*B+1 : ℕ) : ℝ)≤(2*C+1)*scale d := by
  have hunit := one_le_scale d
  push_cast
  nlinarith only [h,hunit]

theorem early_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (horder : d.stage.source.val<d.stage.target.val),
      ((2*ActivePrefixStageFullEarlyRun.cost D d horder+1 : ℕ) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageFullBudget.early_uniform_bound D
  refine ⟨2*C+1,by positivity,?_⟩
  intro s d ho
  apply twice_bound
  simpa only [scale,mul_assoc] using h s d ho

theorem late_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (horder : d.stage.target.val<d.stage.source.val)
      (hn : 0<d.stage.f-1) (hb : 2≤s.guard),
      ((2*ActivePrefixStageFullLateRun.cost D d horder hn hb+1 : ℕ) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageFullBudget.late_uniform_bound D
  refine ⟨2*C+1,by positivity,?_⟩
  intro s d ho hn hb
  apply twice_bound
  simpa only [scale,mul_assoc] using h s d ho hn hb

theorem dispatch_uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hn : 0<d.stage.f-1) (hb : 2≤s.guard),
      ((2*ActivePrefixStageDispatchRun.cost D d hn hb+1 : ℕ) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageDispatchBudget.uniform_bound D
  refine ⟨2*C+1,by positivity,?_⟩
  intro s d hn hb
  apply twice_bound
  simpa only [scale,mul_assoc] using h s d hn hb

end
end IntegerMultBounds.Machine.ActivePrefixStageInverseBudget
