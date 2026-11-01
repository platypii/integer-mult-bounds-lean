module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedCoreMovement

/-! Reconcile the local singleton schedulers with one whole-class raw budget.
All additional setup and postprocessing remain explicit before absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {U : Type}

private theorem rawRecoveryScheduleTimeBudget_cons (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (r : RawRecoveryJob s) (records : List (RawRecoveryJob s)) :
    rawRecoveryScheduleTimeBudget b work (r::records)+10 =
      rawRecoveryScheduleTimeBudget b work [r]+rawRecoveryScheduleTimeBudget b work records := by
  simp only [rawRecoveryScheduleTimeBudget,descriptorScheduleTape,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.length_append]
  omega

/-- Local scheduler entry/exit overhead is linear in job count. The numerical
budget and descriptor traffic are exactly the same whole-list charge. -/
theorem rawRecoverySingletonBudgets_sum (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    (records.map (fun r => rawRecoveryScheduleTimeBudget b work [r])).sum+10 =
      rawRecoveryScheduleTimeBudget b work records+10*records.length := by
  induction records with
  | nil => simp [rawRecoveryScheduleTimeBudget,descriptorScheduleTape]
  | cons r records ih =>
    have hc := rawRecoveryScheduleTimeBudget_cons b work r records
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

noncomputable def computedRecoveryAuxiliaryTime (work : Fin 392 → Fin T) (r : PackedNormalizedJob A s) : ℕ :=
  r.masterInput.timeCost+recoverySeedCopyCost r.rawRecoveryJob.problem r.rawRecoveryJob.W r.Fs.length+
    completeComplexRecoveryHeadersCost r.rawRecoveryJob.problem r.Fs.length+
    recoveryDescriptorProductionCost (A := A) work r.rawRecoveryJob r.Fs.length+
    (9*(descriptorBankTape (placedDescriptorFields work (r.rawRecoveryJob.words (A := A)))).length+5)+
    preparedPairRecoveryOutputCost r.rawRecoveryJob r.Fs.length+
    RecoveryNormalizePlan.cropTimeCost r r.Fs.length+retireRecoveryMastersCost r.rawRecoveryJob.problem

theorem computedNormalizedTime_eq (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (r : PackedNormalizedJob A s) :
    plan.normalizedTimeCost b r = rawRecoveryScheduleTimeBudget b plan.work [r.rawRecoveryJob]+
      computedRecoveryAuxiliaryTime plan.work r := by
  unfold ComputedRecoveryPlan.normalizedTimeCost recoveryLifecycleTime computedRecoveryAuxiliaryTime
  omega

/-- This equality keeps every master/header/normalization/cleanup bill and
replaces all singleton numerical budgets with one schedule budget. -/
theorem computedCoreScheduleTime_eq (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (records : List (PackedNormalizedJob A s)) :
    (records.map (plan.coreTimeCost b V)).sum+10 =
      rawRecoveryScheduleTimeBudget b plan.work (records.map PackedNormalizedJob.rawRecoveryJob)+
        (records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)).sum+
        10*records.length := by
  have hsplit : (records.map (plan.coreTimeCost b V)).sum =
      (records.map (fun r => rawRecoveryScheduleTimeBudget b plan.work [r.rawRecoveryJob])).sum+
        (records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)).sum := by
    induction records with
    | nil => simp
    | cons r records ih =>
      simp only [List.map_cons,List.sum_cons,computedCoreTime_eq,computedNormalizedTime_eq]
      omega
  have hsingle := rawRecoverySingletonBudgets_sum b plan.work (records.map PackedNormalizedJob.rawRecoveryJob)
  rw [hsplit]
  simp only [List.map_map,List.length_map,Function.comp_def] at hsingle
  omega

/-- A whole-class fast raw bound is used once; auxiliary work remains a sum
of actual local bills. No per-core whole-axis reserve is introduced. -/
theorem computedCoreScheduleTime_le_raw (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (records : List (PackedNormalizedJob A s)) (rawBound : ℕ)
    (hraw : rawRecoveryScheduleTimeBudget b plan.work (records.map PackedNormalizedJob.rawRecoveryJob) ≤ rawBound) :
    (records.map (plan.coreTimeCost b V)).sum ≤ rawBound+
      (records.map (fun r => computedRecoveryAuxiliaryTime plan.work r+computedCoreMovementTime V r)).sum+
      10*records.length := by
  have h := computedCoreScheduleTime_eq plan b V records
  omega

end IntegerMultBounds.MathlibTM2.Cost
