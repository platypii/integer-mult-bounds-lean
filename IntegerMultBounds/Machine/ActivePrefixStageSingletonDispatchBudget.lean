import IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatch
import IntegerMultBounds.Machine.ActivePrefixStageSingletonBudget
import IntegerMultBounds.Machine.ActivePrefixStageDispatchBudget

/-! The dynamic singleton direction test and its paid cleanup add only linear
work to the complete singleton stage. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatchBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageSingletonData (Inputs)
open ActivePrefixStageSingletonDispatch

theorem uniform_bound : ∃ C : ℝ,0<C ∧ ∀ {s : Shape} (d : Inputs s),
    (cost d : ℝ)≤C*(d.rows*s.recordWidth : ℕ) := by
  obtain ⟨C,hC,he,hl⟩ := ActivePrefixStageSingletonBudget.uniform_bound
  refine ⟨C+27,by positivity,?_⟩
  intro s d
  have ho : (ActivePrefixStageOrderCompare.cost d.stage : ℝ)+4≤27*(d.rows*s.recordWidth : ℕ) := by
    exact_mod_cast ActivePrefixStageDispatchBudget.overhead d.toInputs
  by_cases h : d.stage.source.val<d.stage.target.val
  · have hs := he d h
    rw [cost,dite_eq_left h]
    push_cast at ho hs ⊢
    nlinarith only [ho,hs]
  · have hs := hl d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h)
    rw [cost,dite_eq_right h]
    push_cast at ho hs ⊢
    nlinarith only [ho,hs]

end IntegerMultBounds.Machine.ActivePrefixStageSingletonDispatchBudget
