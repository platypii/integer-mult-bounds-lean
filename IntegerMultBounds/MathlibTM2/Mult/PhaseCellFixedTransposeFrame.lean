module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedTransposeCaller

/-! Combine worker and generator projections into one exact ambient frame.
The unused suffix slot at 109 is handled by the existing external frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {Q K : ℕ}

theorem initializedCaller_frame (hstates : stateCount ≤ Q) (V : ℕ) (xs : List Bool)
    (S F : Stacks (tapeCount+117) (prime+K))
    (hblank : ∀ r, S.R (callerGenerator (originReg r)) = []) (hcount : S.R (callerGenerator 116) = [])
    (hcounter : F.R (callerGenerator 116) = [])
    (hworker : embStk callerWorker F = (bank hstates).scheduleState V [] xs
      (S.R (callerGenerator 109)) (embStk callerWorker (widthState V S)))
    (hclear : ∀ j : Fin 117, j.val < 31 → F.R (callerGenerator j) = [])
    (hretain : ∀ j : Fin 117, 31 ≤ j.val → j ≠ 109 → j ≠ 116 → (∀ i, callerWorker i ≠ callerGenerator j) →
      F.R (callerGenerator j) = S.R (callerGenerator j)) (hleft : F.L = S.L)
    (hoff : ∀ outside, (∀ j, callerGenerator j ≠ outside) → (∀ i, callerWorker i ≠ outside) →
      F.L outside = S.L outside ∧ F.R outside = S.R outside) :
    F = {widthState V S with R := (Function.update (widthState V S).R
      (callerWorker (workerReg (reg pay))) (xs.map bitSymbol))} := by
  classical
  refine Stacks.ext (congrArg (fun z => z.inp) hworker) (congrArg (fun z => z.out) hworker) hleft ?_
  funext outside
  by_cases hi : ∃ i, callerWorker i = outside
  · obtain ⟨i,rfl⟩ := hi
    have hh := congrArg (fun z => z.R i) hworker
    by_cases hp : i = workerReg (reg pay)
    · subst i
      simpa only [bank,StreamedChunkBank.scheduleState,embStk_R,Function.update_self] using hh
    · have hp' := TransposeRegisterPlacement.worker_injective.ne hp
      by_cases hq : i = control 7
      · subst i
        have heq : callerGenerator 109 = callerWorker (control 7) := rfl
        have hqval : (widthState V S).R (callerWorker (control 7)) = S.R (callerGenerator 109) := by
          rw [←heq,widthState_generator]
        have hqval' : (widthState V S).R (TransposeRegisterPlacement.worker (control 7)) = S.R (callerGenerator 109) := hqval
        simpa only [bank,StreamedChunkBank.scheduleState,StreamedChunkBank.scheduleStream,List.nil_append,embStk_R,callerWorker,Function.update_of_ne hp,
          Function.update_self,Function.update_of_ne hp',hqval'] using hh
      · simpa only [bank,StreamedChunkBank.scheduleState,embStk_R,callerWorker,Function.update_of_ne hp,
          Function.update_of_ne hq,Function.update_of_ne hp'] using hh
  · have heOff : ∀ i, callerWorker i ≠ outside := by simpa using hi
    have hR : F.R outside = S.R outside := by
      by_cases hg : ∃ j, callerGenerator j = outside
      · obtain ⟨j,hj⟩ := hg
        rw [←hj]
        by_cases hj31 : j.val < 31
        · rw [hclear j hj31]
          obtain ⟨r,hr⟩ := originReg_covers j hj31
          rw [←hr]
          exact (hblank r).symm
        · have hj109 : j ≠ 109 := by
            intro h
            subst j
            have heq : callerGenerator 109 = callerWorker (control 7) := rfl
            exact heOff (control 7) (heq.symm.trans hj)
          by_cases hj116 : j = 116
          · subst j; exact hcounter.trans hcount.symm
          · exact hretain j (by omega) hj109 hj116 (by intro i; simpa only [hj] using heOff i)
      · exact (hoff outside (by simpa using hg) heOff).2
    simpa only [widthState,Function.update_of_ne (heOff (workerReg (reg pay))).symm,
      Function.update_of_ne (heOff (control 5)).symm] using hR

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
