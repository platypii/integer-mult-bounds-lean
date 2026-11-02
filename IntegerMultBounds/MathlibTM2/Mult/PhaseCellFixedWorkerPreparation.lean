module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedTransposeCaller

/-! Establish the fixed worker's readiness by copying the retained width.
Fresh arithmetic/private tapes and empty left stacks are ordinary input facts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

theorem control_ne_workerReg (i : Fin 19) (j : Fin (swapT 6)) : control i ≠ workerReg j := by
  have hj := j.isLt
  simp [control,workerReg,Fin.ext_iff]
  omega

def prepareWorker : Pr P (tapeCount+117) Q (prime+K) U :=
  ucopy (callerGenerator 115) (callerWorker (control 5)) (callerGenerator 106)

def widthState (V : ℕ) (S : Stacks (tapeCount+117) (prime+K)) : Stacks (tapeCount+117) (prime+K) :=
  {S with R := Function.update S.R (callerWorker (control 5)) (List.replicate V tick)}

theorem widthState_ready (hstates : stateCount ≤ Q) (V : ℕ)
    (S : Stacks (tapeCount+117) (prime+K))
    (hL : ∀ i, S.L (callerWorker i) = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ control 7 → S.R (callerWorker i) = []) :
    (bank hstates).Ready V (embStk callerWorker (widthState V S)) := by
  have hcontrol (i : Fin 19) (hi5 : i ≠ 5) (hi7 : i ≠ 7) :
      (widthState V S).R (callerWorker (control i)) = [] := by
    simp only [widthState,callerWorker,Function.update_of_ne (TransposeRegisterPlacement.worker_injective.ne (control_injective.ne hi5))]
    exact hfresh _ (control_ne_workerReg _ _) (control_injective.ne hi7)
  have hreg (j : Fin (swapT 6)) (hj : j ≠ reg pay) :
      (widthState V S).R (callerWorker (workerReg j)) = [] := by
    simp only [widthState,callerWorker,Function.update_of_ne (TransposeRegisterPlacement.worker_injective.ne (control_ne_workerReg 5 j).symm)]
    exact hfresh _ (workerReg_injective.ne hj) (control_ne_workerReg 7 j).symm
  refine ⟨?_,?_,?_,hL,?_,?_,?_,?_⟩
  · simp [bank,embStk,widthState]
  · exact hcontrol 6 (by decide) (by decide)
  · intro i hi
    change i ∈ [control 8,control 9,control 10,control 11,control 12]++
      List.ofFn (fun k : Fin 5 => control ⟨k.val,by omega⟩) at hi
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at hi
    rcases hi with (rfl | rfl | rfl | rfl | rfl) | ⟨k,rfl⟩
    all_goals apply hcontrol <;> (simp [Fin.ext_iff] <;> omega)
  · intro j hj
    apply hreg
    intro he
    have hh := congrArg Fin.val he
    change j.val = 5 at hh
    omega
  · intro k
    apply hreg
    intro he
    have hh := congrArg Fin.val he
    change k.val = 5 at hh
    have hk := k.isLt
    omega
  · intro i hi
    change i ∈ [control 13,control 14,control 15,control 16,control 17,control 18] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hcontrol _ (by decide) (by decide)
  · intro i hip hheads s hs
    have heq := hreg (reg i) (by
      intro he
      exact hip (BinaryInterchangeRun.slot_injective he))
    rw [show (embStk callerWorker (widthState V S)).R ((bank hstates).ι (reg i)) = [] from heq] at hs
    exact (List.not_mem_nil hs).elim

theorem prepareWorker_exec (body : P → Pr P (tapeCount+117) Q (prime+K) U)
    (V : ℕ) (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (hwidth : (S.R (callerGenerator 115)).length = V) (hz : S.R (callerGenerator 106) = [])
    (hfresh : S.R (callerWorker (control 5)) = []) :
    ∃ v', v'.user = v.user ∧ Exec body prepareWorker (Host.mk v S) (4*V+4) (Host.mk v' (widthState V S)) := by
  have hsrc := TransposeRegisterPlacement.generator_off_worker (control 7) 115 (by decide) (control 5)
  have htmp := TransposeRegisterPlacement.generator_off_worker (control 7) 106 (by decide) (control 5)
  obtain ⟨v',hu,he⟩ := ucopy_exec (body := body) hsrc
    ((TransposeRegisterPlacement.generator_injective (control 7)).ne (by decide : (115 : Fin 117) ≠ 106))
    htmp.symm v S hz
  have hw : (S.R (TransposeRegisterPlacement.generator (control 7) 115)).length = V := hwidth
  have hf : S.R (TransposeRegisterPlacement.worker (control 5)) = [] := hfresh
  exact ⟨v',hu,by simpa only [prepareWorker,widthState,callerGenerator,callerWorker,hw,hf,List.append_nil] using he⟩

theorem width_off_generator (j : Fin 117) : callerGenerator j ≠ callerWorker (control 5) := by
  change TransposeRegisterPlacement.generator (control 7) j ≠ TransposeRegisterPlacement.worker (control 5)
  by_cases hj : j = 109
  · subst j
    rw [TransposeRegisterPlacement.generator_queue]
    exact TransposeRegisterPlacement.worker_injective.ne (control_injective.ne (by decide : (7 : Fin 19) ≠ 5))
  · exact TransposeRegisterPlacement.generator_off_worker (control 7) j hj (control 5)

theorem widthState_generator (V : ℕ) (S : Stacks (tapeCount+117) (prime+K)) (j : Fin 117) :
    (widthState V S).R (callerGenerator j) = S.R (callerGenerator j) := by
  simp only [widthState,Function.update_of_ne (width_off_generator j)]

theorem prepareWorker_native : mnNativePushBound 3 (prepareWorker (P := P) (Q := Q) (K := K) (U := U)) := by
  simp [prepareWorker,ucopy,umulSym,scanR,drainR,popDo,whileR,keepIn,pushN,
    moveR,moveStep,peekR,mnNativePushBound,mnActPush]

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
