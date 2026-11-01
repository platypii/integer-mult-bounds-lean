module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryPreparation
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleBudgetCosts

/-! The actual computed-call stock separates numerical workspace from linear
preparation and movement traffic. No numerical time bound is used for storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {U : Type}

private theorem masterStock_le_time (d : InverseMasterInput s) : d.stock ≤ 3*d.timeCost := by
  unfold InverseMasterInput.stock InverseMasterInput.timeCost InverseMasterInput.masters generateInverseMastersCost
  omega

private theorem cropStock_le_time (r : PackedNormalizedJob A s) (N : ℕ) :
    RecoveryNormalizePlan.cropStock r N ≤ 13*RecoveryNormalizePlan.cropTimeCost r N := by
  unfold RecoveryNormalizePlan.cropStock RecoveryNormalizePlan.cropTimeCost RecoveryNormalizePlan.queueTimeCost
  omega

theorem computedNormalizedStock_le (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (r : PackedNormalizedJob A s) (Cprog : ℕ) :
    plan.normalizedStock b r Cprog ≤ 18*computedRecoveryAuxiliaryTime plan.work r+
      (Cprog+1)*rawRecoveryScheduleWorkspaceBudget b plan.work [r.rawRecoveryJob] := by
  have hm := masterStock_le_time r.masterInput
  have hc := cropStock_le_time r r.Fs.length
  unfold ComputedRecoveryPlan.normalizedStock recoveryLifecycleStock computedRecoveryAuxiliaryTime
  nlinarith only [hm,hc]

theorem computedCoreStock_le (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (r : PackedNormalizedJob A s) (Cprog : ℕ) :
    plan.coreStock b V r Cprog ≤ 18*(computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)+
      (Cprog+1)*rawRecoveryScheduleWorkspaceBudget b plan.work [r.rawRecoveryJob] := by
  have h := computedNormalizedStock_le plan b r Cprog
  unfold ComputedRecoveryPlan.coreStock computedCoreMovementTime
  nlinarith only [h]

theorem computedCoreStock_sum_le (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V Cprog : ℕ) (records : List (PackedNormalizedJob A s)) :
    (records.map (fun r => plan.coreStock b V r Cprog)).sum ≤
      18*(records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)).sum+
      (Cprog+1)*(records.map (fun r => rawRecoveryScheduleWorkspaceBudget b plan.work [r.rawRecoveryJob])).sum := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have h := computedCoreStock_le plan b V r Cprog
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [h,ih]

/-- Singleton schedulers retain separate entry overhead, but their descriptor
traffic and output volumes are exactly the corresponding whole-class sums. -/
theorem rawRecoverySingletonWorkspaceBudgets_sum_le (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    (records.map (fun r => rawRecoveryScheduleWorkspaceBudget b work [r])).sum ≤
      (records.map RawRecoveryJob.outputVolume).sum+7*(records.map b.stock).sum+
      (2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
        (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        6*records.length)+2366*records.length := by
  induction records with
  | nil => simp [descriptorScheduleTape]
  | cons r records ih =>
    have h := rawRecoveryScheduleWorkspaceBudget_le b work [r]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.length_append,Nat.add_zero,
      ] at h ⊢
    unfold descriptorScheduleTape at ih
    omega

end IntegerMultBounds.MathlibTM2.Cost
