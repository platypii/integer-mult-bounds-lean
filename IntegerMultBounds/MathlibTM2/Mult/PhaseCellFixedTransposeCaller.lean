module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedStreamedBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransposeRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedTransposeCaller

/-! Instantiate the physical transpose with one fixed worker and register
placement. Table initialization is executed from retained binary headers. -/
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
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (ha : S.R (callerGenerator 97) = binSyms V a) (hb : S.R (callerGenerator 98) = binSyms V b)
    (hseed : S.R (callerGenerator 102) = binSyms V C) (hz : S.R (callerGenerator 106) = [])
    (hwidth : (S.R (callerGenerator 115)).length = V)
    (hblank : ∀ r, S.R (callerGenerator (originReg r)) = [])
    (hcount : S.R (callerGenerator 116) = [])
    (hready : (bank hstates).Ready V (embStk callerWorker S))
    (hsrc : (embStk callerWorker S).R ((bank hstates).ι (reg (bank hstates).pay)) =
      (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (110*V+137+32921*(V+1)^5)+(rs.map (fun r => (bank hstates).stageTimeCost V
        (∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((330*V+411+98763*(V+1)^5)+(bank hstates).scheduleStockAllowance V rs)) depth
        (caller hstates) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R (callerGenerator 116) = [] ∧
      embStk callerWorker F = (bank hstates).scheduleState V [] (keyReplicaWords f)
        (S.R (callerGenerator 109)) (embStk callerWorker S) ∧
      (∀ j : Fin 117, j.val < 31 → F.R (callerGenerator j) = []) ∧
      (∀ j : Fin 117, 31 ≤ j.val → j ≠ 109 → j ≠ 116 → (∀ i, callerWorker i ≠ callerGenerator j) →
        F.R (callerGenerator j) = S.R (callerGenerator j)) ∧
      ∀ outside, (∀ j, callerGenerator j ≠ outside) → (∀ i, callerWorker i ≠ outside) →
        F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  exact (bank hstates).generatedTransposeCaller_exec_within body callerGenerator
    (TransposeRegisterPlacement.generator_injective _) callerWorker
    TransposeRegisterPlacement.worker_injective
    (TransposeRegisterPlacement.generator_bank_off _) (by rfl)
    (TransposeRegisterPlacement.count_off _) a b C V hC hbits hfit
    f v S ha hb hseed hz hwidth hblank hcount hready hsrc

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
