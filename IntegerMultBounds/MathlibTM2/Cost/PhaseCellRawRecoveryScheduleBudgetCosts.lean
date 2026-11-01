module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryScheduleBudgets
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryBudgetEstimates

/-! Expose the actual scheduler bills in the terms already bounded by the
caller, descriptor and restoring-cleanup estimates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s T Q A : ℕ} [NeZero s] {U : Type}

theorem rawRecoveryScheduleTimeBudget_eq (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    rawRecoveryScheduleTimeBudget b work records =
      (records.map RawRecoveryJob.timeBudget).sum+
      (records.map (fun r => 6*b.stock r+2358)).sum+
      (2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
        (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        6*records.length)+3*records.length+10 := by
  have heq (xs : List (RawRecoveryJob s)) :
      (xs.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+
        r.timeBudget+(6*b.stock r+2358)+3)).sum =
      (xs.map RawRecoveryJob.timeBudget).sum+(xs.map (fun r => 6*b.stock r+2358)).sum+
        (xs.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        3*xs.length := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      ring
  unfold rawRecoveryScheduleTimeBudget
  rw [heq]
  ring

private theorem foldr_max_le_sum (xs : List ℕ) : xs.foldr max 0 ≤ xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons,List.sum_cons]
    omega

/-- The trace retains a single peak; its numerical upper bound can use summed
scratch because shared setup has already been amortized across the schedule. -/
theorem rawRecoveryScheduleWorkspaceBudget_le (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) :
    rawRecoveryScheduleWorkspaceBudget b work records ≤
      (records.map RawRecoveryJob.outputVolume).sum+7*(records.map b.stock).sum+
      (2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+
        (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        6*records.length)+2358*records.length+8 := by
  have heq (xs : List (RawRecoveryJob s)) :
      (xs.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+
        b.stock r+(6*b.stock r+2358))).sum =
      (xs.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A))))).sum+
        7*(xs.map b.stock).sum+2358*xs.length := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [ih]
      ring
  have hp := foldr_max_le_sum (records.map (fun r =>
    takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+b.stock r+(6*b.stock r+2358)))
  rw [heq] at hp
  unfold rawRecoveryScheduleWorkspaceBudget
  omega

end IntegerMultBounds.MathlibTM2.Cost
