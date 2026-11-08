module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketBatchLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPacketWorker

/-! Apply one retained diagonal page to a batch using one shared workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s t α p w c n T Q A : ℕ} [NeZero s] [NeZero t]
  {P U : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem diagonalBatch_exec
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (clock count queue saved tmp : Fin T) (x y o : RsbR) (hfree : RsbFree x y o)
    (hreg : [clock,count,queue,rg x,rg o,saved,tmp].Nodup)
    (hoff : ∀ r, rg r ≠ queue) (hclockOff : ∀ r, rg r ≠ clock)
    (hqueueWork : ∀ j, queue ≠ ι j) (hclockWork : ∀ j, clock ≠ ι j)
    (ρ : RsbR → List (Fin (A+4))) (hr : RsbReady ρ w p) (hw : p+2 ≤ w)
    (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (Ds : List (ZMod s → GaussianInt)) (hfit : c+n ≤ s)
    (hD : ∀ D ∈ Ds, ∀ z ∈ packedInterval c n D, Fits w z)
    (hy : ρ y = cstream A w (packedInterval c n (diagonalField s t α p)))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hqueue : S.R queue = (Ds.flatMap (fun D => cstream A w (packedInterval c n D)))++tail)
    (hclock : (S.R clock).length = Ds.length) (hcount : (S.R count).length = n*w)
    (hinput : S.R (rg x) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hclean : RsbClean ι S) (hS : RsbHolds rg S ρ) :
    ∃ v' F steps, v'.user = v.user ∧
      steps ≤ Ds.length*((6*(n*w)+6)+(n*(rmulCost w+6*w+2)+8)+(2*(n*w)+2)+3)+2 ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(6*(n*w)+6)+realWeightWorkspace C w n)) depth
        (countedLoop clock (diagonalPacketWorker (rg := rg) count queue saved tmp x y o hι hT hQ))
        (Host.mk v S) steps (Host.mk v' F)) ∧
      F.R clock = [] ∧ F.R queue = tail ∧
      F.R (rg o) = (Ds.reverse.flatMap (fun D => cstream A w (packedInterval c n (diagonalProduct s t α p D))))++S.R (rg o) ∧
      F.R (rg y) = S.R (rg y) ∧ F.R (rg x) = [] ∧
      F = {S with R := (Function.update (Function.update (Function.update S.R clock []) queue tail)
        (rg o) (Ds.reverse.flatMap (fun D => cstream A w (packedInterval c n
          (diagonalProduct s t α p D)))++S.R (rg o)))} := by
  have hregs := hreg
  regs_ne hregs
  let Ready : Stacks T A → Prop := fun F => RsbClean ι F ∧
    (∀ r, r ≠ o → F.R (rg r) = ρ r) ∧ (F.R count).length = n*w ∧ F.R saved = [] ∧ F.R tmp = []
  have hin : ρ x = [] := (hS x).symm.trans hinput
  have hclockStable : ∀ F word, Ready F → Ready {F with R := Function.update F.R clock word} := by
    intro F word hR
    refine ⟨⟨hR.1.1,?_⟩,?_,?_,?_,?_⟩
    · intro j; simpa only [Function.update_of_ne (hclockWork j).symm] using hR.1.2 j
    · intro r hr; simpa only [Function.update_of_ne (hclockOff r)] using hR.2.1 r hr
    · simpa only [Function.update_of_ne ‹clock ≠ count›.symm] using hR.2.2.1
    · simpa only [Function.update_of_ne ‹clock ≠ saved›.symm] using hR.2.2.2.1
    · simpa only [Function.update_of_ne ‹clock ≠ tmp›.symm] using hR.2.2.2.2
  have hpacketStable : ∀ F tail packet, Ready F →
      Ready {F with R := Function.update (Function.update F.R queue tail) (rg o) (packet++F.R (rg o))} := by
    intro F tail packet hR
    refine ⟨⟨hR.1.1,?_⟩,?_,?_,?_,?_⟩
    · intro j
      simpa only [Function.update_of_ne (hdisj o j).symm,Function.update_of_ne (hqueueWork j).symm] using hR.1.2 j
    · intro r hr
      simpa only [Function.update_of_ne (fun he => hr (hrg he)),Function.update_of_ne (hoff r)] using hR.2.1 r hr
    · simpa only [Function.update_of_ne ‹count ≠ rg o›,Function.update_of_ne ‹count ≠ queue›] using hR.2.2.1
    · simpa only [Function.update_of_ne ‹rg o ≠ saved›.symm,Function.update_of_ne ‹queue ≠ saved›.symm] using hR.2.2.2.1
    · simpa only [Function.update_of_ne ‹rg o ≠ tmp›.symm,Function.update_of_ne ‹queue ≠ tmp›.symm] using hR.2.2.2.2
  let input := fun D : ZMod s → GaussianInt => cstream A w (packedInterval c n D)
  let output := fun D : ZMod s → GaussianInt => cstream A w (packedInterval c n (diagonalProduct s t α p D))
  let cost := (6*(n*w)+6)+(n*(rmulCost w+6*w+2)+8)+(2*(n*w)+2)
  have hworker : ∀ D ∈ Ds, ∀ (vi : HS T Q A U) F tail, Ready F → F.R queue = input D++tail →
      ∃ vf steps, vf.user = vi.user ∧ steps ≤ cost ∧
        ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk vi F)+depth+
          (2*(6*(n*w)+6)+realWeightWorkspace C w n)) depth
          (diagonalPacketWorker (rg := rg) count queue saved tmp x y o hι hT hQ) (Host.mk vi F) steps
          (Host.mk vf {F with R := Function.update (Function.update F.R queue tail) (rg o) (output D++F.R (rg o))}) := by
    intro D hmem vi F tail hR hq
    let σ := Function.update ρ o (F.R (rg o))
    have hh : RsbHolds rg F σ := by
      intro r; by_cases hr : r = o
      · subst r; simp [σ]
      · simpa only [σ,Function.update_of_ne hr] using hR.2.1 r hr
    obtain ⟨vf,steps,hu,hn,_,ht,_⟩ := diagonalPacketWorker_exec (body := body) hrg hdisj hι hT hQ hA
      count queue saved tmp x y o hfree (by regs_nodup) hoff hqueueWork σ
      (hr.update o (fun c => (hfree.2.2.2 c).2.2) _) hw hp hα hαp D hfit (hD D hmem)
      (by simpa only [σ,Function.update_of_ne hfree.2.2.1] using hy) C hpush vi F tail hq
      hR.2.2.1 ((hR.2.1 x hfree.2.1).trans hin) hR.2.2.2.1 hR.2.2.2.2 hR.1 hh
    exact ⟨vf,steps,hu,hn,ht⟩
  obtain ⟨v',F,steps,hu,hn,ht,hc,hR,hq,ho,hfinal⟩ := packetBatchLoop_exec clock queue (rg o) (by regs_nodup)
    _ Ds input output (fun _ => cost) _ Ready hclockStable hpacketStable
    (by intro D _; simp only [input,output,length_cstream,packedInterval_length _ hfit]) hworker v S tail hclock
    ⟨hclean,(fun r _ => hS r),hcount,hsaved,htmp⟩ hqueue
  refine ⟨v',F,steps,hu,?_,ht,hc,hq,ho,(hR.2.1 y hfree.2.2.1).trans (hS y).symm,
    (hR.2.1 x hfree.2.1).trans hin,hfinal⟩
  simpa only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id,cost] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
