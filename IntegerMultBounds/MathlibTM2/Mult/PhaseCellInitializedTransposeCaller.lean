module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedWorkerPreparation

/-! First execution of the fixed transpose from a fresh worker and retained
headers. Width preparation is executed once and leaves the worker reusable. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

def initializedCaller (hstates : stateCount ≤ Q) : Pr P (tapeCount+117) Q (prime+K) U :=
  .seq prepareWorker (caller hstates)

theorem initializedCaller_exec_within (body : P → Pr P (tapeCount+117) Q (prime+K) U)
    (hstates : stateCount ≤ Q) (a b C V : ℕ) (hC : 0 < C)
    (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (ha : S.R (callerGenerator 97) = binSyms V a) (hb : S.R (callerGenerator 98) = binSyms V b)
    (hseed : S.R (callerGenerator 102) = binSyms V C) (hz : S.R (callerGenerator 106) = [])
    (hwidth : (S.R (callerGenerator 115)).length = V)
    (hblank : ∀ r, S.R (callerGenerator (originReg r)) = [])
    (hcount : S.R (callerGenerator 116) = [])
    (hL : ∀ i, S.L (callerWorker i) = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ control 7 → S.R (callerWorker i) = [])
    (hsrc : S.R (callerWorker (workerReg (reg pay))) = (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (114*V+141+32921*(V+1)^5)+(rs.map (fun r => (bank hstates).stageTimeCost V
        (∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((342*V+423+98763*(V+1)^5)+(bank hstates).scheduleStockAllowance V rs)) depth
        (initializedCaller hstates) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R (callerGenerator 116) = [] ∧
      embStk callerWorker F = (bank hstates).scheduleState V [] (keyReplicaWords f)
        (S.R (callerGenerator 109)) (embStk callerWorker (widthState V S)) ∧
      (∀ j : Fin 117, j.val < 31 → F.R (callerGenerator j) = []) ∧
      (∀ j : Fin 117, 31 ≤ j.val → j ≠ 109 → j ≠ 116 → (∀ i, callerWorker i ≠ callerGenerator j) →
        F.R (callerGenerator j) = S.R (callerGenerator j)) ∧
      (bank hstates).Ready V (embStk callerWorker F) ∧
      F.L = S.L ∧
      ∀ outside, (∀ j, callerGenerator j ≠ outside) → (∀ i, callerWorker i ≠ outside) →
        F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  have hf := hfresh (control 5) (control_ne_workerReg _ _)
    (control_injective.ne (by decide : (5 : Fin 19) ≠ 7))
  obtain ⟨v₁,hu₁,he₁⟩ := prepareWorker_exec body V v S hwidth hz hf
  have hp : (widthState V S).R (callerWorker (workerReg (reg pay))) = (replicaKeyWords f).map bitSymbol := by
    simpa only [widthState,callerWorker,Function.update_of_ne
      (TransposeRegisterPlacement.worker_injective.ne (control_ne_workerReg 5 _).symm)] using hsrc
  obtain ⟨v₂,F,m,hu₂,hm,ht,hcounter,hF,hclear,hretain,hleft,hoff⟩ := caller_exec_within body hstates a b C V hC hbits hfit f
    v₁ (widthState V S)
    (by rw [widthState_generator]; exact ha) (by rw [widthState_generator]; exact hb)
    (by rw [widthState_generator]; exact hseed) (by rw [widthState_generator]; exact hz)
    (by rw [widthState_generator]; exact hwidth)
    (by intro r; rw [widthState_generator]; exact hblank r)
    (by rw [widthState_generator]; exact hcount) (widthState_ready hstates V S hL hfresh) hp
  have hstock : (∑ j, ((embStk callerWorker (widthState V S)).R ((bank hstates).ι j)).length) =
      ∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [bank,embStk_R,widthState,callerWorker,Function.update_of_ne
      (TransposeRegisterPlacement.worker_injective.ne (control_ne_workerReg 5 j).symm)]
  rw [hstock] at hm
  refine ⟨v₂,F,(4*V+4)+m,hu₂.trans hu₁,by omega,?_,hcounter,?_,hclear,?_,?_,hleft,?_⟩
  · intro depth
    have hp := mn_native_exec_within he₁ 3 prepareWorker_native depth
      (mnSize (Host.mk v S)+depth+(12*V+12)) (by omega)
    have hs := mn_seq_within_add hp (ht depth)
    exact hs.mono (by intro d z hz; omega)
  · simpa only [widthState_generator] using hF
  · intro j hj hj109 hj116 hi
    rw [hretain j hj hj109 hj116 hi,widthState_generator]
  · rw [hF]
    exact (bank hstates).scheduleState_ready V [] (keyReplicaWords f)
      ((widthState V S).R (callerGenerator 109)) (embStk callerWorker (widthState V S))
      (widthState_ready hstates V S hL hfresh)
  · intro outside hg he
    refine ⟨(hoff outside hg he).1,?_⟩
    rw [(hoff outside hg he).2]
    exact Function.update_of_ne (he (control 5)).symm _ _

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
