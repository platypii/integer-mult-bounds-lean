import IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeBudget
import IntegerMultBounds.Machine.ActivePrefixStageInverseBudget

/-! Complete width-and-direction round trips pay both physical runs and the
join while retaining the certified exponent uniformly across all widths. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeData (Packed cost)
open ActivePrefixStageInverseBudget (scale twice_bound)

theorem uniform_bound (D : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hp : 1<d.stage.f → Packed d D),
      ((2*cost D d hp+1 : ℕ) : ℝ)≤C*scale d := by
  obtain ⟨C,hC,h⟩ := ActivePrefixStageRuntimeBudget.uniform_bound D
  refine ⟨2*C+1,by positivity,?_⟩
  intro s d hp
  apply twice_bound
  simpa only [scale,mul_assoc] using h s d hp

end IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseBudget
