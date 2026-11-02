module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringTransposeCaller
public import IntegerMultBounds.MathlibTM2.Host.EmbedOwnedUpdateStock

/-! Place the actual restoring bit-plane kernel over a background without
charging spectator storage again. Its budget depends only on dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def restoringTimeCost (hstates : stateCount ≤ Q) (a b C V : ℕ) : ℕ :=
  (116*V+143+32921*(V+1)^5)+
    (((dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)).map
      (fun r => (bank hstates).stageTimeCost V (2^a*2^b*C) r+3)).sum+2

def restoringStockAllowance (hstates : stateCount ≤ Q) (a b C V : ℕ) : ℕ :=
  (342*V+423+98763*(V+1)^5)+(bank hstates).scheduleStockAllowance V
    ((dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims))

theorem placedRestoring_exec_within (body : P → Pr P T Q (prime+K) U)
    (e : Fin (tapeCount+117) → Fin T) (he : Function.Injective e)
    (hstates : stateCount ≤ Q) (a b C V : ℕ) (hC : 0 < C)
    (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool) (depth : ℕ)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (ha : S.R (e (callerGenerator 97)) = binSyms V a)
    (hb : S.R (e (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (e (callerGenerator 102)) = binSyms V C)
    (hz : S.R (e (callerGenerator 106)) = [])
    (hwidth : (S.R (e (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (e (callerGenerator (originReg r))) = [])
    (hcount : S.R (e (callerGenerator 116)) = [])
    (hL : ∀ i, S.L (e (callerWorker i)) = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ control 7 → S.R (e (callerWorker i)) = [])
    (hsrc : S.R (e (callerWorker (workerReg (reg pay)))) = (replicaKeyWords f).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoringTimeCost hstates a b C V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+restoringStockAllowance hstates a b C V)
        depth (embProg e Empty.elim (restoringCaller (P := Empty) hstates)) (mk v S) n
        (mk v' {S with R := (Function.update S.R (e (callerWorker (workerReg (reg pay))))
          ((keyReplicaWords f).map bitSymbol))}) := by
  obtain ⟨v₁,n,hu,hn,ht⟩ := restoringCaller_exec_within (fun z : Empty => nomatch z) hstates a b C V hC
    hbits hfit f (embDn e v) (embStk e S) ha hb hseed hz hwidth hblank hcount hL hfresh hsrc
  have hstock : (∑ j, ((embStk callerWorker (embStk e S)).R ((bank hstates).ι j)).length) = 2^a*2^b*C :=
    freshBankStock_eq a b C f (embStk e S) hfresh hsrc
  rw [hstock] at hn
  obtain ⟨v',hu',ht'⟩ := exec_emb_owned_update_within e he (fun z : Empty => nomatch z)
    (callerWorker (workerReg (reg pay))) ((keyReplicaWords f).map bitSymbol) v S (ht depth)
  exact ⟨v',n,hu'.trans hu,hn,ht'⟩

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
