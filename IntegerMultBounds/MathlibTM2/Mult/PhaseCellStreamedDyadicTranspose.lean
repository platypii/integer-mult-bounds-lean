module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedScheduleExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposeWiring

/-! A complete exact dyadic transpose from a binary schedule stream, executed
by one fixed worker bank and an external consuming counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace StreamedChunkBank
variable {t₀ T T' Q K a b W : ℕ} {P U : Type}

theorem dyadicTranspose_exec_within (body : P → Pr P T' Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count)
    (plan : DyadicTransposePlan a b W) (hW : 0 < W) (V : ℕ)
    (hfit : ∀ r ∈ plan.wiredStages (fun _ => bank.dims), ∀ k,
      swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits k < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin W → Bool) (tail : List (Fin (prime+K+4)))
    (v : HS T' Q (prime+K) U) (S : Stacks T' (prime+K))
    (hready : bank.Ready V (embStk e S))
    (hcount : (S.R count).length = (plan.wiredStages (fun _ => bank.dims)).length)
    (hqueue : (embStk e S).R bank.queue =
      bank.scheduleStream V (plan.wiredStages (fun _ => bank.dims))++tail)
    (hsrc : (embStk e S).R (bank.ι (reg bank.pay)) = (replicaKeyWords f).map bitSymbol) :
    let rs := plan.wiredStages (fun _ => bank.dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => bank.stageTimeCost V (∑ j, ((embStk e S).R (bank.ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        bank.scheduleStockAllowance V rs) depth
        (countedLoop count (embProg e Empty.elim (bank.program (P := Empty))))
        (Host.mk v S) n (Host.mk v' F)) ∧ F.R count = [] ∧
      embStk e F = bank.scheduleState V [] (keyReplicaWords f) tail (embStk e S) := by
  let rs := plan.wiredStages (fun _ => bank.dims)
  have hgeometry := plan.wiredStages_ready (fun _ => bank.dims) hW
  obtain ⟨v',F,n,hu,hn,htrace,hc,hF⟩ := bank.schedule_exec_within body e he count hoff V (2^a*2^b*W) rs
    (by intro r hr; exact (hgeometry r hr).1)
    (by intro r hr; exact (hgeometry r hr).2.1) hfit
    (by intro r hr; exact (hgeometry r hr).2.2)
    (replicaKeyWords f) (by simp [replicaKeyWords,Nat.mul_assoc]) tail v S hready hcount hqueue hsrc
  refine ⟨v',F,n,hu,hn,htrace,hc,?_⟩
  simpa only [rs,plan.wiredStages_words] using hF

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
