module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedChunkInterchangeStock

/-! Fixed streamed-routing wiring and ordinary reusable-bank readiness.
Queue contents and the owned payload are deliberately outside readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure StreamedChunkBank (t₀ T Q : ℕ) where
  hd : Fin 5 → Fin t₀
  pay : Fin t₀
  hi : Function.Injective hd
  hpay : ∀ k, hd k ≠ pay
  hQ : swapStates hd pay hi ≤ Q
  ι : Fin (swapT t₀) → Fin T
  hι : Function.Injective ι
  hT : swapT t₀ ≤ T
  dims : Fin 5 → Fin T
  hdims : Function.Injective dims
  width : Fin T
  zero : Fin T
  queue : Fin T
  binary : Fin T
  duplicate : Fin T
  readerWork : Fin T
  saved : Fin T
  tmp : Fin T
  a : Fin T
  half : Fin T
  par : Fin T
  bits : Fin T
  cnt : Fin T
  work : Fin T
  hreader : ∀ k, [width,zero,queue,binary,dims k,duplicate,readerWork,saved,tmp].Nodup
  hgen : ∀ k, [dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup
  hdimOff : ∀ k j, dims k ≠ ι j
  hqueueOff : ∀ j, queue ≠ ι j
  hqueueControls : ∀ i ∈ [a,half,par,bits,cnt,work], queue ≠ i
  hprotected : ∀ i ∈ [width,zero,binary,duplicate,readerWork,saved,tmp,a,half,par,bits,cnt,work]++List.ofFn dims,
    i ≠ queue ∧ i ≠ ι (reg pay)

namespace StreamedChunkBank
variable {t₀ T Q K : ℕ}

noncomputable def program {P U : Type} (bank : StreamedChunkBank t₀ T Q) : Pr P T Q (prime+K) U :=
  streamedChunkInterchange bank.hd bank.pay bank.hi bank.hQ bank.ι bank.hι bank.hT bank.dims
    bank.width bank.zero bank.queue bank.binary bank.duplicate bank.readerWork bank.saved bank.tmp
    bank.a bank.half bank.par bank.bits bank.cnt bank.work

structure Ready (bank : StreamedChunkBank t₀ T Q) (V : ℕ) (S : Stacks T (prime+K)) : Prop where
  hwidth : (S.R bank.width).length = V
  hzero : S.R bank.zero = []
  hblank : ∀ i ∈ [bank.binary,bank.duplicate,bank.readerWork,bank.saved,bank.tmp]++List.ofFn bank.dims, S.R i = []
  hL : ∀ i, S.L i = []
  hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank.ι j) = []
  hhdr : ∀ k, S.R (bank.ι (reg (bank.hd k))) = []
  hgenBlank : ∀ i ∈ [bank.a,bank.half,bank.par,bank.bits,bank.cnt,bank.work], S.R i = []
  hother : ∀ i, i ≠ bank.pay → (∀ k, bank.hd k ≠ i) →
    ∀ s ∈ S.R (bank.ι (reg i)), s ≠ blank ∧ s.val < prime+4

theorem Ready.of_frame (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (S F : Stacks T (prime+K)) (h : bank.Ready V S) (hL : ∀ i, F.L i = [])
    (hframe : ∀ i, i ≠ bank.queue → i ≠ bank.ι (reg bank.pay) → F.R i = S.R i) :
    bank.Ready V F := by
  have hp : ∀ i ∈ [bank.width,bank.zero,bank.binary,bank.duplicate,bank.readerWork,bank.saved,bank.tmp,
      bank.a,bank.half,bank.par,bank.bits,bank.cnt,bank.work]++List.ofFn bank.dims, F.R i = S.R i := by
    intro i hi
    exact hframe i (bank.hprotected i hi).1 (bank.hprotected i hi).2
  have hb (i : Fin (swapT t₀)) (hi : i ≠ reg bank.pay) : F.R (bank.ι i) = S.R (bank.ι i) :=
    hframe _ (bank.hqueueOff i).symm (by intro he; exact hi (bank.hι he))
  refine ⟨?_,?_,?_,hL,?_,?_,?_,?_⟩
  · rw [hp bank.width (by simp)]; exact h.hwidth
  · rw [hp bank.zero (by simp)]; exact h.hzero
  · intro i hi
    rw [hp i (by
      rcases List.mem_append.mp hi with hi | hi
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
      · exact List.mem_append_right _ hi)]
    exact h.hblank i hi
  · intro j hj
    rw [hb j (by
      intro he
      have hh := congrArg Fin.val he
      change j.val = bank.pay.val at hh
      have hh' := bank.pay.isLt
      omega)]
    exact h.hpriv j hj
  · intro k
    rw [hb _ (by
      intro he
      exact bank.hpay k (BinaryInterchangeRun.slot_injective he))]
    exact h.hhdr k
  · intro i hi
    rw [hp i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    exact h.hgenBlank i hi
  · intro i hip hheads s hs
    rw [hb _ (by intro he; exact hip (BinaryInterchangeRun.slot_injective he))] at hs
    exact h.hother i hip hheads s hs

theorem Ready.stage_exec_within {P U : Type} (body : P → Pr P T Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (V outerCount blockWidth h d : ℕ)
    (hfit : ∀ k, swapValues outerCount 1 blockWidth h d k < 2^V)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1) (houter : 0 < outerCount) (hblock : 0 < blockWidth)
    (xs : List Bool) (hlen : xs.length = BinaryAdjacentWidthInterchange.volume outerCount (2^h) 1 (2^d) blockWidth)
    (tail : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hready : bank.Ready V S)
    (hqueue : S.R bank.queue = ((interchangeDimensionRow bank.dims outerCount blockWidth h d).flatMap
      fun p => binSyms V p.1)++tail)
    (hsrc : S.R (bank.ι (reg bank.pay)) = xs.map bitSymbol) (depth : ℕ) :
    let row := interchangeDimensionRow bank.dims outerCount blockWidth h d
    let F : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update
      (Function.update S.R bank.queue tail) (bank.ι (reg bank.pay))
      ((swapList outerCount (2^h) 1 (2^d) blockWidth false xs).map bitSymbol))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ readDimensionRowCost V row+
        generatedBalancedChunkInterchangeCost T t₀ outerCount blockWidth h d (∑ j, (S.R (bank.ι j)).length)+
        (2*(row.map Prod.fst).sum+2*row.length+1) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        3*readDimensionRowCost V row+generatedChunkStockAllowance T outerCount blockWidth h d)
        depth bank.program (Host.mk v S) n (Host.mk v' F) ∧
      mnSize (Host.mk v' F) ≤ mnSize (Host.mk v S) ∧ bank.Ready V F := by
  obtain ⟨v',n,hu,hn,he,hs⟩ := streamedChunkInterchange_exec_within body bank.hd bank.pay bank.hi bank.hpay
    bank.hQ bank.ι bank.hι bank.hT bank.dims bank.hdims bank.width bank.zero bank.queue bank.binary
    bank.duplicate bank.readerWork bank.saved bank.tmp bank.a bank.half bank.par bank.bits bank.cnt bank.work
    bank.hreader bank.hgen bank.hdimOff bank.hqueueOff bank.hqueueControls V outerCount blockWidth h d
    hfit hhd hdh houter hblock xs hlen tail v S hready.hwidth hready.hzero hqueue hready.hblank
    hready.hL hready.hpriv hready.hhdr hready.hgenBlank hsrc hready.hother depth
  refine ⟨v',n,hu,hn,he,hs,?_⟩
  apply Ready.of_frame bank V S _ hready (by intro i; rfl)
  intro i hq hp
  simp only [Function.update_of_ne hp,Function.update_of_ne hq]

theorem Ready.stage_exec_uniform {P U : Type} (body : P → Pr P T Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (V outerCount blockWidth h d : ℕ)
    (hfit : ∀ k, swapValues outerCount 1 blockWidth h d k < 2^V)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1) (houter : 0 < outerCount) (hblock : 0 < blockWidth)
    (xs : List Bool) (hlen : xs.length = BinaryAdjacentWidthInterchange.volume outerCount (2^h) 1 (2^d) blockWidth)
    (tail : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hready : bank.Ready V S)
    (hqueue : S.R bank.queue = ((interchangeDimensionRow bank.dims outerCount blockWidth h d).flatMap
      fun p => binSyms V p.1)++tail)
    (hsrc : S.R (bank.ι (reg bank.pay)) = xs.map bitSymbol) :
    let row := interchangeDimensionRow bank.dims outerCount blockWidth h d
    let F : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update
      (Function.update S.R bank.queue tail) (bank.ι (reg bank.pay))
      ((swapList outerCount (2^h) 1 (2^d) blockWidth false xs).map bitSymbol))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ readDimensionRowCost V row+
        generatedBalancedChunkInterchangeCost T t₀ outerCount blockWidth h d (∑ j, (S.R (bank.ι j)).length)+
        (2*(row.map Prod.fst).sum+2*row.length+1) ∧
      (∀ depth, ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        3*readDimensionRowCost V row+generatedChunkStockAllowance T outerCount blockWidth h d)
        depth bank.program (Host.mk v S) n (Host.mk v' F)) ∧
      mnSize (Host.mk v' F) ≤ mnSize (Host.mk v S) ∧ bank.Ready V F := by
  obtain ⟨v',n,hu,hn,he,hs,hF⟩ := hready.stage_exec_within body bank V outerCount blockWidth h d
    hfit hhd hdh houter hblock xs hlen tail v S hqueue hsrc 0
  refine ⟨v',n,hu,hn,?_,hs,hF⟩
  intro depth
  obtain ⟨vf,m,hu',hm,htrace,hs',hF'⟩ := hready.stage_exec_within body bank V outerCount blockWidth h d
    hfit hhd hdh houter hblock xs hlen tail v S hqueue hsrc depth
  obtain ⟨hsteps,hfinal⟩ := he.toExec.unique htrace.toExec
  rw [←hsteps,←hfinal] at htrace
  exact htrace

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
