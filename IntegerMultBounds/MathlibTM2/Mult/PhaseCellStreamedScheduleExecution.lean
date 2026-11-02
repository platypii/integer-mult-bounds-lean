module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedScheduleData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedListBankLoopStock

/-! Execute a complete binary-driven interchange schedule in one fixed worker
bank. The invariant records a completed prefix and the exact remaining frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace StreamedChunkBank
variable {t₀ T T' Q K : ℕ} {P U : Type}

theorem schedule_exec_within (body : P → Pr P T' Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (e : Fin T → Fin T') (he : Function.Injective e)
    (count : Fin T') (hoff : ∀ i, e i ≠ count)
    (V volume : ℕ) (rs : List (BalancedChunkInterchangeStage T))
    (hpositive : ∀ r ∈ rs, 0 < r.outerCount ∧ 0 < r.blockWidth)
    (hbalance : ∀ r ∈ rs, r.leftBits ≤ r.rightBits+1 ∧ r.rightBits ≤ r.leftBits+1)
    (hfit : ∀ r ∈ rs, ∀ k, swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits k < 2^V)
    (hvolume : ∀ r ∈ rs, volume = BinaryAdjacentWidthInterchange.volume r.outerCount
      (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth)
    (xs : List Bool) (hxs : xs.length = volume) (tail : List (Fin (prime+K+4)))
    (v : HS T' Q (prime+K) U) (S : Stacks T' (prime+K))
    (hready : bank.Ready V (embStk e S)) (hcount : (S.R count).length = rs.length)
    (hqueue : (embStk e S).R bank.queue = bank.scheduleStream V rs++tail)
    (hsrc : (embStk e S).R (bank.ι (reg bank.pay)) = xs.map bitSymbol) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => bank.stageTimeCost V (∑ j, ((embStk e S).R (bank.ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        bank.scheduleStockAllowance V rs) depth
        (countedLoop count (embProg e Empty.elim (bank.program (P := Empty))))
        (Host.mk v S) n (Host.mk v' F)) ∧ F.R count = [] ∧
      embStk e F = bank.scheduleState V [] (balancedChunkStageBits rs xs) tail (embStk e S) := by
  let S₀ := embStk e S
  have hsrc₀ : S₀.R (bank.ι (reg bank.pay)) = xs.map bitSymbol := hsrc
  have hqueue₀ : S₀.R bank.queue = bank.scheduleStream V rs++tail := hqueue
  let stock := ∑ j, (S₀.R (bank.ι j)).length
  let Inv := fun remaining F => ∃ done bits,
    rs = done++remaining ∧ bits = balancedChunkStageBits done xs ∧ bits.length = volume ∧
      F = bank.scheduleState V remaining bits tail S₀
  have hstep : ∀ r ∈ rs, ∀ remaining (vi : HS T Q (prime+K) U) F, Inv (r::remaining) F →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ bank.stageTimeCost V stock r ∧
        (∀ depth, ExecWithin (fun z : Empty => nomatch z)
          (fun d z => mnSize z+d ≤ mnSize (Host.mk vi F)+depth+bank.scheduleStockAllowance V rs)
          depth bank.program (Host.mk vi F) n (Host.mk vf G)) ∧
        Inv remaining G ∧ mnSize (Host.mk vf G) ≤ mnSize (Host.mk vi F) := by
    intro r hr remaining vi F hI
    obtain ⟨done,bits,hsplit,hbits,hbitsLen,hF⟩ := hI
    subst F
    let M := bank.scheduleState V (r::remaining) bits tail S₀
    have hM : bank.Ready V M := bank.scheduleState_ready V _ _ _ _ hready
    have hq : M.R bank.queue = ((interchangeDimensionRow bank.dims r.outerCount r.blockWidth r.leftBits r.rightBits).flatMap
        fun p => binSyms V p.1)++(bank.scheduleStream V remaining++tail) := by
      simp only [M,scheduleState,Function.update_of_ne (bank.hqueueOff (reg bank.pay)),Function.update_self,
        scheduleStream,List.append_assoc]
    have hp : M.R (bank.ι (reg bank.pay)) = bits.map bitSymbol := by
      simp only [M,scheduleState,Function.update_self]
    have hstock : (∑ j, (M.R (bank.ι j)).length) = stock := by
      apply bank.scheduleState_bankStock
      simpa only [hsrc₀,List.length_map] using hbitsLen.trans hxs.symm
    obtain ⟨vf,n,hu,hn,htrace,hs,hG⟩ := hM.stage_exec_uniform
      (fun z : Empty => nomatch z) bank V r.outerCount r.blockWidth r.leftBits r.rightBits
      (hfit r hr) (hbalance r hr).1 (hbalance r hr).2 (hpositive r hr).1 (hpositive r hr).2
      bits (hbitsLen.trans (hvolume r hr)) (bank.scheduleStream V remaining++tail) vi M hq hp
    let ys := swapList r.outerCount (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth false bits
    have hys : ys.length = volume :=
      (swapList_bitSymbols_length bits (hbitsLen.trans (hvolume r hr))).trans hbitsLen
    have hnext := bank.scheduleState_step V (r::remaining) remaining bits ys tail S₀
    change {M with L := (fun _ => []), R := (Function.update
      (Function.update M.R bank.queue (bank.scheduleStream V remaining++tail))
      (bank.ι (reg bank.pay)) (ys.map bitSymbol))} = bank.scheduleState V remaining ys tail S₀ at hnext
    rw [hnext] at htrace hs
    refine ⟨vf,bank.scheduleState V remaining ys tail S₀,n,hu,?_,?_,?_,hs⟩
    · simpa only [stageTimeCost,hstock] using hn
    · intro depth
      exact (htrace depth).mono (J := fun d z => mnSize z+d ≤ mnSize (Host.mk vi M)+depth+
        bank.scheduleStockAllowance V rs) (by
        intro d z hz
        have hh := bank.stageStockAllowance_le V rs r hr
        have hz' : mnSize z+d ≤ mnSize (Host.mk vi M)+depth+bank.stageStockAllowance V r := by
          simpa only [stageStockAllowance,Nat.add_assoc] using hz
        omega)
    · refine ⟨done++[r],ys,?_,?_,hys,rfl⟩
      · simpa only [List.append_assoc,List.singleton_append] using hsplit
      · rw [balancedChunkStageBits_append]
        simp only [ys,balancedChunkStageBits,hbits]
  have hinitial : Inv rs S₀ := by
    refine ⟨[],xs,rfl,rfl,hxs,?_⟩
    symm
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; exact (hready.hL i).symm
    · change Function.update (Function.update S₀.R bank.queue (bank.scheduleStream V rs++tail))
        (bank.ι (reg bank.pay)) (xs.map bitSymbol) = S₀.R
      rw [←hqueue₀,←hsrc₀]
      simp only [Function.update_eq_self]
  obtain ⟨v',F,n,hu,hn,htrace,hc,hI⟩ := countedListBankLoop_exec_within (body := body) e he count hoff
    bank.program rs (bank.stageTimeCost V stock) Inv (bank.scheduleStockAllowance V rs)
    hstep v S hcount hinitial
  refine ⟨v',F,n,hu,hn,htrace,hc,?_⟩
  obtain ⟨done,bits,hsplit,hbits,hbitsLen,hF⟩ := hI
  have hd : done = rs := by simpa only [List.append_nil] using hsplit.symm
  subst done
  rw [hbits] at hF
  exact hF

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
