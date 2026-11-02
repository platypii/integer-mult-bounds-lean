module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedDyadicTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedEmbeddedFrame

/-! Execute the arithmetic generator's metadata with one reusable worker bank.
Per-stage fit, schedule identity and count matching are derived here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace StreamedChunkBank
variable {t₀ T T' Q K a b W : ℕ} {P U : Type}

theorem generatedDyadicTranspose_exec_within (body : P → Pr P T' Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count)
    (hW : 0 < W) (V : ℕ)
    (hbits : a+b < V) (hfit : W*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin W → Bool) (tail : List (Fin (prime+K+4)))
    (v : HS T' Q (prime+K) U) (S : Stacks T' (prime+K))
    (hready : bank.Ready V (embStk e S))
    (hcount : (S.R count).length = dyadicStageCount (a+b) a b)
    (hqueue : (embStk e S).R bank.queue =
      (dyadicScheduleValues (a+b) a b W).flatMap (binSyms V)++tail)
    (hsrc : (embStk e S).R (bank.ι (reg bank.pay)) = (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b W (by omega)).wiredStages (fun _ => bank.dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => bank.stageTimeCost V (∑ j, ((embStk e S).R (bank.ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        bank.scheduleStockAllowance V rs) depth
        (countedLoop count (embProg e Empty.elim (bank.program (P := Empty))))
        (Host.mk v S) n (Host.mk v' F)) ∧ F.R count = [] ∧
      embStk e F = bank.scheduleState V [] (keyReplicaWords f) tail (embStk e S) ∧
      ∀ outside, outside ≠ count → (∀ i, e i ≠ outside) →
        F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  have hc : (S.R count).length =
      ((dyadicTransposePlan (a+b) a b W (by omega)).wiredStages (fun _ => bank.dims)).length := by
    simpa only [bank.canonicalScheduleLength] using hcount
  have hq : (embStk e S).R bank.queue = bank.scheduleStream V
      ((dyadicTransposePlan (a+b) a b W (by omega)).wiredStages (fun _ => bank.dims))++tail := by
    simpa only [bank.canonicalScheduleStream] using hqueue
  obtain ⟨v',F,n,hu,hn,htrace,hcounter,hF⟩ := bank.dyadicTranspose_exec_within body e he count hoff
    (dyadicTransposePlan (a+b) a b W (by omega)) hW V
    (bank.canonicalScheduleFit a b W V hbits hfit) f tail v S hready hc hq hsrc
  refine ⟨v',F,n,hu,hn,htrace,hcounter,hF,?_⟩
  intro outside hc hoff
  exact countedEmbedded_preserves_external e count outside (bank.program (P := Empty)) hc.symm hoff
    (htrace 0).toExec

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
