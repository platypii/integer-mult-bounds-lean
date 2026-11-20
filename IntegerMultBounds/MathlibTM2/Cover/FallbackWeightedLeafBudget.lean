module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafRun
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-! Charge weighted leaves at their actual terminal widths and volumes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine RecursiveInterchangeLayout M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def weightedLeafRate [M8.Machine.Net] (tapes push : ℕ) (L : ℝ) : ℝ :=
  (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)+
    2*(|LeafCore.C| * L*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125+448)

theorem weightedLeafCost_le [M8.Machine.Net] (N width tapes push : ℕ) {L : ℝ}
    (widthBound : ((max 1 width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L) :
    (weightedLeafCost N width tapes push : ℝ) ≤ weightedLeafRate tapes push L*N := by
  have core := RevBudget.coreCost_le N width widthBound
  unfold weightedLeafCost weightedLeafBodyCost weightedLeafRate
  push_cast
  calc
    _ ≤ (1+186*(push : ℝ))*((3*(210*(2*((prime.size : ℝ)+1)^2)+16120+100)+387)*N+
        2*((|LeafCore.C| * N*L)*((tapes : ℝ)+5)))+(12000*(1+186*(push : ℝ))+125)*N + 448*N := by gcongr
    _ = _ := by ring

/-- Successive good records retain the parent's volume. Their linear overheads
add, and the terminal interchange pays for the width left after all gaps. -/
theorem weightedLeaf_chain_cost [M8.Machine.Net] {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (tapes push : ℕ) (L : ℝ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    time [] child ≤ weightedLeafCost (volume prime child) child.width tapes push →
    ((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ L →
    (time records v : ℝ) ≤ (weightedLeafRate tapes push L+(records.map overhead).sum)*(volume prime v : ℝ) := by
  intro child terminal widthBound
  have same : volume prime child = volume prime v := rankDescriptor_volume v (Nat.sub_add_cancel fits).symm
  have leaf := weightedLeafCost_le (volume prime child) child.width tapes push widthBound
  have chain := rankDescriptor_chain_time gap overhead time step records v fits
  calc
    (time records v : ℝ) ≤ ((time [] child + (records.map overhead).sum * volume prime v : ℕ) : ℝ) :=
      Nat.cast_le.mpr chain
    _ ≤ _ := by
      push_cast
      rw [add_mul]
      apply add_le_add_left
      rw [← same]
      exact (Nat.cast_le.mpr terminal).trans leaf

end IntegerMultBounds.MathlibTM2.Cover.Fallback
