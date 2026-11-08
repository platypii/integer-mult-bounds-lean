module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedListLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiringPacketWorker

/-! A fixed consuming worker traverses packets with one shared workspace reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U E : Type} {body : P → Pr P T Q A U}

theorem packetBatchLoop_exec (clock queue out : Fin T) (hreg : [clock,queue,out].Nodup)
    (worker : Pr P T Q A U) (rs : List E) (input output : E → List (Fin (A+4)))
    (cost : E → ℕ) (reserve : ℕ) (Ready : Stacks T A → Prop)
    (hclockStable : ∀ S word, Ready S → Ready {S with R := Function.update S.R clock word})
    (hpacketStable : ∀ S tail packet, Ready S →
      Ready {S with R := Function.update (Function.update S.R queue tail) out (packet++S.R out)})
    (hlen : ∀ r ∈ rs, (output r).length = (input r).length)
    (hworker : ∀ r ∈ rs, ∀ (v : HS T Q A U) S tail, Ready S → S.R queue = input r++tail →
      ∃ v' n, v'.user = v.user ∧ n ≤ cost r ∧
        ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+reserve)
          depth worker (Host.mk v S) n
          (Host.mk v' {S with R := Function.update (Function.update S.R queue tail) out (output r++S.R out)}))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hcount : (S.R clock).length = rs.length) (hReady : Ready S)
    (hqueue : S.R queue = rs.flatMap input++tail) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (rs.map (fun r => cost r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+reserve)
        depth (countedLoop clock worker) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R clock = [] ∧ Ready F ∧ F.R queue = tail ∧
      F.R out = rs.reverse.flatMap output++S.R out ∧
      F = {S with R := (Function.update (Function.update (Function.update S.R clock []) queue tail)
        out (rs.reverse.flatMap output++S.R out))} := by
  have hr := hreg
  regs_ne hr
  let Frame : Stacks T A → Prop := fun F => F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    ∀ k, k ≠ clock → k ≠ queue → k ≠ out → F.R k = S.R k
  let Inv : List E → Stacks T A → Prop := fun xs F =>
    ∃ done : List E, rs = done++xs ∧ Ready F ∧ F.R queue = xs.flatMap input++tail ∧
      F.R out = done.reverse.flatMap output++S.R out ∧ Frame F
  have hstable : ∀ xs F word, Inv xs F → Inv xs {F with R := Function.update F.R clock word} := by
    intro xs F word hI
    obtain ⟨done,heq,hR,hq,ho,hF⟩ := hI
    exact ⟨done,heq,hclockStable F word hR,by simpa [‹clock ≠ queue›.symm] using hq,
      by simpa [‹clock ≠ out›.symm] using ho,hF.1,hF.2.1,hF.2.2.1,
      fun k hc hq ho => (Function.update_of_ne hc _ _).trans (hF.2.2.2 k hc hq ho)⟩
  have hstep : ∀ r ∈ rs, ∀ xs (vi : HS T Q A U) F, Inv (r::xs) F →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ cost r ∧
        (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk vi F)+depth+reserve)
          depth worker (Host.mk vi F) n (Host.mk vf G)) ∧
        G.R clock = F.R clock ∧ Inv xs G ∧ mnSize (Host.mk vf G) ≤ mnSize (Host.mk vi F) := by
    intro r hr xs vi F hI
    obtain ⟨done,heq,hR,hq,ho,hF⟩ := hI
    have hq' : F.R queue = input r++(xs.flatMap input++tail) := by
      simpa only [List.flatMap_cons,List.append_assoc] using hq
    obtain ⟨vf,n,hu,hn,ht⟩ := hworker r hr vi F (xs.flatMap input++tail) hR hq'
    let G : Stacks T A := {F with R := Function.update (Function.update F.R queue (xs.flatMap input++tail)) out (output r++F.R out)}
    refine ⟨vf,G,n,hu,hn,ht,?_,?_,?_⟩
    · simp [G,‹clock ≠ out›,‹clock ≠ queue›]
    · refine ⟨done++[r],?_,hpacketStable F _ _ hR,?_,?_,hF.1,hF.2.1,hF.2.2.1,?_⟩
      · simpa only [List.append_assoc,List.singleton_append] using heq
      · simp [G,‹queue ≠ out›]
      · simp only [G,Function.update_self,ho,List.reverse_append,List.reverse_singleton,
          List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
      · intro k hc hq ho
        exact (Function.update_of_ne ho _ _).trans
          ((Function.update_of_ne hq _ _).trans (hF.2.2.2 k hc hq ho))
    · exact (packet_replace_preserves_size queue out ‹queue ≠ out›.symm (input r) (output r)
        (xs.flatMap input++tail) (hlen r hr) vi vf F hq').le
  obtain ⟨v',F,n,hu,hn,ht,hc,hF⟩ := countedListLoop_exec_within clock worker rs cost Inv reserve hstable hstep
    v S hcount ⟨[],by simp,hReady,hqueue,by simp,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩
  obtain ⟨done,heq,hR,hq,ho,hframe⟩ := hF
  have hdone : done = rs := by simpa only [List.append_nil] using heq.symm
  have hqueueF : F.R queue = tail := by simpa using hq
  have houtF : F.R out = rs.reverse.flatMap output++S.R out := by simpa only [hdone] using ho
  refine ⟨v',F,n,hu,hn,ht,hc,hR,hqueueF,houtF,?_⟩
  refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
  funext k
  by_cases ho : k = out
  · subst k; simpa only [Function.update_self] using houtF
  · by_cases hq : k = queue
    · subst k; simpa only [Function.update_of_ne ho,Function.update_self] using hqueueF
    · by_cases hk : k = clock
      · subst k; simpa only [Function.update_of_ne ho,Function.update_of_ne hq,Function.update_self] using hc
      · simpa only [Function.update_of_ne ho,Function.update_of_ne hq,Function.update_of_ne hk]
          using hframe.2.2.2 k hk hq ho

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
