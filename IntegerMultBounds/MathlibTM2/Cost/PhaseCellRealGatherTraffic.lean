module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeRealGather

/-! Price physical exposure without replacing padded volume by real volume.
The inverse route remains explicit; all other traffic has a linear replica bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem retireDummyBatchesCost_le (rows capacity B P : ℕ) (hfit : rows ≤ capacity) :
    retireDummyBatchesCost rows capacity B P ≤
      B*(10*(capacity*P)+6*P+9)+17*capacity+30 := by
  have hsetup := paddingCounterSetupCost_le (width := B*P) hfit
  have hpad := Nat.mul_le_mul_right (B*P) (Nat.sub_le capacity rows)
  unfold retireDummyBatchesCost retireDummyRowsCost
  nlinarith only [hsetup,hpad]

variable {t₀ T Q c d W K : ℕ}

theorem realGatherTimeCost_le (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B : ℕ) (S : Stacks T (prime+K))
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d) :
    plan.realGatherTimeCost V s width radius L w B S ≤ plan.inverseCost S+
      6*((2^d)^c*(L*w))+34*(2^d)^c+64+
      B*(replicaCoreGatherStepCost V s width radius L w+2*(s*w)+16*((2^d)^c*(L*w))+6*(L*w)+27) := by
  subst B
  have hsetup := gatherCounterSetupCost_le (width := L*w) hcapacity
  have hretire := retireDummyBatchesCost_le _ _ (2^d) (L*w) hcapacity
  unfold ArchiveTilePlan.realGatherTimeCost replicaCoreGatherLoopCost
  nlinarith only [hsetup,hretire]

theorem realGatherStockAllowance_le (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d) :
    plan.realGatherStockAllowance V s width radius L w B ≤ plan.inverseStockAllowance+
      3*replicaCoreGatherStepCost V s width radius L w+16*((2^d)^c*(L*w))+68*(2^d)^c+122+
      B*(21*((2^d)^c*(L*w))+12*(L*w)+18) := by
  subst B
  have hsetup := gatherCounterSetupCost_le (width := L*w) hcapacity
  have hretire := retireDummyBatchesCost_le _ _ (2^d) (L*w) hcapacity
  have hsplit := congrArg (fun x => (2^d)*(x*(L*w))) (Nat.sub_add_cancel hcapacity)
  unfold ArchiveTilePlan.realGatherStockAllowance
  nlinarith only [hsetup,hretire,hsplit]

/-- The advertised physical bill contains padded volume explicitly. Any
further absorption must justify its capacity choice or sharpen this bill. -/
theorem paddedVolume_le_realGatherTimeCost (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B : ℕ) (S : Stacks T (prime+K)) :
    6*(B*((2^d)^c*(L*w))) ≤ plan.realGatherTimeCost V s width radius L w B S := by
  calc
    _ = B*(6*((2^d)^c*L*w)) := by ring
    _ ≤ B*(6*((2^d)^c*L*w)+13) := Nat.mul_le_mul_left B (Nat.le_add_right _ _)
    _ ≤ _ := by unfold ArchiveTilePlan.realGatherTimeCost; omega

end IntegerMultBounds.MathlibTM2.Cost
