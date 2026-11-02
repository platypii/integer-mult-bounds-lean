module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedStreamedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransposeRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedTransposeCaller

/-! Instantiate the physical transpose with one fixed worker and register
placement. Only machine state capacity and ordinary input contents remain. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

def callerWorker : Fin tapeCount → Fin (tapeCount+117) := TransposeRegisterPlacement.worker

def callerGenerator : Fin 117 → Fin (tapeCount+117) :=
  TransposeRegisterPlacement.generator (control 7)

def caller (hstates : stateCount ≤ Q) : Pr P (tapeCount+117) Q (prime+K) U :=
  (bank hstates).generatedTransposeCaller callerGenerator callerWorker

theorem caller_exec_within (body : P → Pr P (tapeCount+117) Q (prime+K) U)
    (hstates : stateCount ≤ Q) (a b C V : ℕ) (hC : 0 < C)
    (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (st : TblSt 16 (prime+K)) (ha : st.val 6 = a) (hb : st.val 7 = b)
    (hseed : st.val 9 = C) (hacc : st.acc = []) (hbound : ∀ j, st.val j < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (hS : tblHolds originReg (embStk callerGenerator S)
      (tblRho V (List.replicate V tick) (List.replicate V tick) st))
    (hcount : S.R (callerGenerator 116) = [])
    (hready : (bank hstates).Ready V (embStk callerWorker S))
    (hsrc : (embStk callerWorker S).R ((bank hstates).ι (reg (bank hstates).pay)) =
      (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ 32921*(V+1)^5+(rs.map (fun r => (bank hstates).stageTimeCost V
        (∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (98763*(V+1)^5+(bank hstates).scheduleStockAllowance V rs)) depth
        (caller hstates) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R (callerGenerator 116) = [] ∧
      embStk callerWorker F = (bank hstates).scheduleState V [] (keyReplicaWords f)
        (S.R (callerGenerator 109)) (embStk callerWorker S) ∧
      (∀ j : Fin 117, j.val < 31 → F.R (callerGenerator j) = []) ∧
      ∀ outside, (∀ j, callerGenerator j ≠ outside) → (∀ i, callerWorker i ≠ outside) →
        F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  exact (bank hstates).generatedTransposeCaller_exec_within body callerGenerator
    (TransposeRegisterPlacement.generator_injective _) callerWorker
    TransposeRegisterPlacement.worker_injective
    (TransposeRegisterPlacement.generator_bank_off _) (by rfl)
    (TransposeRegisterPlacement.count_off _) a b C V hC hbits hfit st ha hb hseed hacc hbound
    f v S hS hcount hready hsrc

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
