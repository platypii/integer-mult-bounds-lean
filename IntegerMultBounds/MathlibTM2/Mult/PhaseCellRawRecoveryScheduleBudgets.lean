module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBudgetedRawRecoverySchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryProgramBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryResourceBudgets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverSchedule

/-! Raw descriptor jobs execute normalization and complete cached recovery.
The fixed restoring schedule retains one peak private scratch allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def rawRecoveryScheduleTimeBudget (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) : ℕ :=
  (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+
    r.timeBudget+(6*b.stock r+2358)+3)).sum+6*records.length+
    2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+10

noncomputable def rawRecoveryScheduleWorkspaceBudget (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (records : List (RawRecoveryJob s)) : ℕ :=
  (records.map RawRecoveryJob.outputVolume).sum+
    (records.map (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+
      b.stock r+(6*b.stock r+2358))).foldr max 0+
    6*records.length+2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+8

theorem rawRecoverySchedule_exec
    (b : RawRecoveryProgramBounds Q A U)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (RawRecoveryJob s))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result b.hR b.hQ
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ rawRecoveryScheduleTimeBudget b work records ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ RawRecoveryJob.output records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*rawRecoveryScheduleWorkspaceBudget b work records) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  exact budgetedRawRecoveryJobSchedule_exec (body := body) b.hR b.hQ b.hA b.R b.K b.hpushR b.hpushK
    b.push b.c b.hpush b.M b.hpushM work hwork src saved count tmp spare result clock savedClock hreg hsep
    records v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
