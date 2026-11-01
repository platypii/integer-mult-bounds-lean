module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobSchedule
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

theorem budgetedRawRecoveryJobSchedule_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M)
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
    let step := normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    let load := fun r : RawRecoveryJob s => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))
    let cleanup := fun r => 6*r.stockBudget hR hQ push c M R K+2358
    let scratch := fun r => load r+r.stockBudget hR hQ push c M R K+cleanup r
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => load r+r.timeBudget+cleanup r+3)).sum+6*records.length+
        2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+10 ∧
      Exec body (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
        (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ RawRecoveryJob.output records outputs ∧
      ∀ C, mnProgPush (descriptorSolverSchedule src saved tmp clock savedClock step) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map RawRecoveryJob.outputVolume).sum+(records.map scratch).foldr max 0+
            6*records.length+2*(descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records).length+8)) depth
          (descriptorSolverSchedule src saved tmp clock savedClock step) (mk v S) n
          (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  exact rawRecoveryJobSchedule_exec (body := body) hR hQ hA R K hpushR hpushK push c hpush M hpushM
    work hwork src saved count tmp spare result clock savedClock hreg hsep records
    RawRecoveryJob.timeBudget (fun r => r.stockBudget hR hQ push c M R K)
    (by
      intro r _ B
      exact ⟨(r.runTime_eq_budget B).le,(r.runStock_eq_budget B hR hQ push c M R K).le⟩)
    v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
