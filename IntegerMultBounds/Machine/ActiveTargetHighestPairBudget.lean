import IntegerMultBounds.Machine.ActiveTargetHighestPairRun

/-! Highest-bit setup and execution is linear in the original full volume;
width-one interchanges introduce no residual fractional-power factor. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairBudget
open ActiveTargetHighestPairData ActiveTargetHighestPairRun

def bits (g : Geometry) := W g+1+g.K

theorem original_volume (g : Geometry) : volume g=g.rows*(2^bits g*g.payload) := by
  unfold volume P gap suffix bits W RadixRangePadding.volume
  simp only [pow_add,pow_one]
  ring

theorem absorbed (g : Geometry) (hrecord : bits g+1≤g.payload) : W g+6≤2*suffix g := by
  have hW : 2≤W g := by have := g.positiveLeft; unfold W; omega
  have hp : g.payload≤suffix g := Nat.le_mul_of_pos_left _ (by positivity)
  unfold bits at hrecord
  omega

theorem uniform_bound : ∃ C : ℝ,0<C ∧ ∀ (g : Geometry) (hs : Fin 10 → List Bool),
    (∀ i,Counter.value (hs i)=values g i) → (∀ i,GrowingCounterData.Canonical (hs i)) →
    (earlierCost g : ℝ)≤C*volume g ∧ (laterCost g hs : ℝ)≤C*volume g := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualShared.uniform_bound
  refine ⟨2*C+ActivePrefixDirtyControlLoad.constant+2,by positivity,?_⟩
  intro g hs hv hc
  have hh := hbound (P g) (gap g) (suffix g) 1 (swapHeaders hs)
    (by have := g.positiveRows; unfold P; positivity) (by unfold gap; positivity)
    (by have := g.positivePayload; unfold suffix; positivity) (swap_values g hs hv)
    (by intro i; fin_cases i <;> exact hc _)
  simp only [max_self,pow_one,Nat.cast_one,Real.one_rpow,mul_one] at hh
  have hV : (1 : ℝ)≤volume g := by
    have : 0<volume g := by
      have := g.positiveRows
      have := g.positivePayload
      unfold volume P gap suffix RadixRangePadding.volume
      positivity
    exact_mod_cast this
  change (swapCost g hs : ℝ)≤C*volume g at hh
  constructor
  · unfold earlierCost
    push_cast
    nlinarith
  · unfold laterCost earlierCost
    push_cast
    nlinarith

end IntegerMultBounds.Machine.ActiveTargetHighestPairBudget
