module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob
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

theorem rawRecoveryJobSchedule_exec
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
    (records : List (RawRecoveryJob s)) (time stock : RawRecoveryJob s → ℕ)
    (hbudget : ∀ r ∈ records, ∀ B : ReplicaRecoveryBatch r.problem r.target r.solution,
      r.runTime B ≤ time r ∧ r.runStock hR hQ push c M R K B ≤ stock r)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work (RawRecoveryJob.words (A := A)) records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A) work src saved count tmp spare result hR hQ
    let load := fun r : RawRecoveryJob s => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))
    let cleanup := fun r => 6*stock r+2358
    let scratch := fun r => load r+stock r+cleanup r
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => load r+time r+cleanup r+3)).sum+6*records.length+
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
  dsimp only
  have hreg' : [src,saved,count,tmp,spare,result].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hsep' (i : Fin 392) : work i ∉ [src,saved,count,tmp,spare,result] := by
    have hh := hsep i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢
    tauto
  obtain ⟨v',n,outputs,hu,hn,he,hgood,htrace⟩ := descriptorSolverSchedule_exec_trace_with_peak_on (body := body)
    work hwork (id : Fin 392 → Fin 392) src saved count tmp spare result clock savedClock hreg hsep
    (RawRecoveryJob.words (A := A)) (normalizedRecoveryDescriptorStep work src saved count tmp spare result hR hQ)
    (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+time r+(6*stock r+2358))
    (fun r => takeDescriptorBankCost (placedDescriptorFields work (r.words (A := A)))+stock r+(6*stock r+2358))
    RawRecoveryJob.output records v S
    (by
      intro r hr vi Si tail hb hl hsrc hc ht hs
      exact normalizedRecoveryDescriptorStep_exec (body := body) r.problem r.W r.inputFields r.fields r.precision_fit r.format_fit hR hQ hA r.span_fit r.origin_lt R K hpushR hpushK
        r.padding r.precision_ge r.width_fit r.target push c hpush M hpushM r.solution r.solves r.sizing
        (time r) (stock r) (hbudget r hr) work hwork src saved count tmp spare result hreg' hsep'
        vi Si tail hb hl hsrc hc ht hs)
    rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  refine ⟨v',n,outputs,hu,hn,he,hgood,?_⟩
  intro C hp hb depth
  simpa only [RawRecoveryJob.outputs_length hgood] using (htrace C hp hb depth).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
