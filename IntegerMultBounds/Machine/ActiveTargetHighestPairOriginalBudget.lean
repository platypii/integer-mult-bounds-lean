import IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalRun
import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersBudget
import IntegerMultBounds.Machine.ActiveTargetHighestPairBudget

/-! The full original-input highest-bit machines retain a linear volume
bound including physical metadata preparation, execution and erasure. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalBudget
open ActiveTargetHighestPairData ActiveTargetHighestPairOriginalRun
open ActiveTargetHighestPairHeadersEndpoint

theorem uniform_bound : ∃ C : ℝ,0<C ∧ ∀ g : Geometry,
    (earlierCost g : ℝ)≤C*volume g ∧ (laterCost g : ℝ)≤C*volume g := by
  obtain ⟨C,hC,hbound⟩ := ActiveTargetHighestPairBudget.uniform_bound
  let H := ActiveTargetHighestPairHeadersBudget.constant
  let E := ActiveTargetHighestPairHeadersBudget.cleanupConstant
  refine ⟨C+H+E+2,by positivity,?_⟩
  intro g
  have hm := hbound g (words g) (words_value g) (words_canonical g)
  have hh : (ActiveTargetHighestPairHeadersRun.cost g : ℝ)≤H*volume g := by
    exact_mod_cast ActiveTargetHighestPairHeadersBudget.cost_bound g
  have he : (ActiveTargetHighestPairHeadersRun.cleanupCost g : ℝ)≤E*volume g := by
    exact_mod_cast ActiveTargetHighestPairHeadersBudget.cleanup_bound g
  have hV : (1 : ℝ)≤volume g := by
    exact_mod_cast ActiveTargetHighestPairHeadersBudget.volume_positive g
  unfold earlierCost laterCost cost
  push_cast
  constructor <;> nlinarith [hm.1,hm.2]

end IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalBudget
