module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedTransposeCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicRectangleSizing
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellStreamedDyadicTransposeBudget

/-! The actual first transpose execution has the sharp complete routing bill.
The fresh bank contains exactly the payload; no stock multiplier is supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
variable {Q K : ℕ} {P U : Type}

theorem freshTransposeBankStock_eq (a b C : ℕ)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool) (S : Stacks (tapeCount+117) (prime+K))
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (callerWorker i) = [])
    (hsrc : S.R (callerWorker (workerReg (reg pay))) = (replicaKeyWords f).map bitSymbol) :
    (∑ j : Fin (swapT 6), (S.R (callerWorker (workerReg j))).length) = 2^a*2^b*C := by
  calc
    _ = (S.R (callerWorker (workerReg (reg pay)))).length := by
      apply Finset.sum_eq_single (reg pay)
      · intro j hj hne
        rw [hfresh _ (workerReg_injective.ne hne) (control_ne_workerReg 7 j).symm]
        rfl
      · simp
    _ = _ := by rw [hsrc]; simp [replicaKeyWords,Nat.mul_assoc]

theorem initializedTranspose_sized_exec_within (body : P → Pr P (tapeCount+117) Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b C : ℕ) (hb : 0 < b) (hC : 0 < C)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (haSrc : S.R (callerGenerator 97) = binSyms (dyadicWordWidth a b C) a)
    (hbSrc : S.R (callerGenerator 98) = binSyms (dyadicWordWidth a b C) b)
    (hseed : S.R (callerGenerator 102) = binSyms (dyadicWordWidth a b C) C)
    (hz : S.R (callerGenerator 106) = [])
    (hwidth : (S.R (callerGenerator 115)).length = dyadicWordWidth a b C)
    (hblank : ∀ r, S.R (callerGenerator (originReg r)) = []) (hcount : S.R (callerGenerator 116) = [])
    (hL : ∀ i, S.L (callerWorker i) = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (callerWorker i) = [])
    (hsrc : S.R (callerWorker (workerReg (reg pay))) = (replicaKeyWords f).map bitSymbol) :
    let V := dyadicWordWidth a b C
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧
      (n : ℝ) ≤ (114*V+141+32921*(V+1)^5 : ℕ)+
        (generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ)*
          ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((342*V+423+98763*(V+1)^5)+streamedDyadicStockCoeff tapeCount*(2^a*2^b*C))) depth
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
  let V := dyadicWordWidth a b C
  obtain ⟨hbits,hfit,hV⟩ := dyadicWordWidth_gates a b C hC
  obtain ⟨v',F,n,hu,hn,ht,hcounter,hF,hclear,hretain,hready,hleft,hoff⟩ := initializedCaller_exec_within body
    hstates a b C V hC hbits hfit f v S haSrc hbSrc hseed hz hwidth hblank hcount hL hfresh hsrc
  have hstock : (∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length) = 2^a*2^b*C :=
    freshTransposeBankStock_eq a b C f S hfresh hsrc
  rw [hstock] at hn
  have htime := canonicalDyadicScheduleTime_le (bank hstates) (a+b) a b C V 1 (2^a*2^b*C)
    hb (by omega) hC (by omega) hV
  have hs := dyadicTransposeScheduleStock_le (bank hstates) (dyadicTransposePlan (a+b) a b C (by omega)) V hC hV
  refine ⟨v',F,n,hu,?_,?_,hcounter,hF,hclear,hretain,hready,hleft,hoff⟩
  · have hnR : (n : ℝ) ≤ (114*V+141+32921*(V+1)^5 : ℕ)+
        (((dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)).map
          (fun r => (bank hstates).stageTimeCost V (2^a*2^b*C) r+3)).sum+2 := by exact_mod_cast hn
    linarith only [hnR,htime]
  · intro depth
    exact (ht depth).mono (by
      intro d z hz
      dsimp only [V] at hs hz ⊢
      omega)

end IntegerMultBounds.MathlibTM2.Cost
