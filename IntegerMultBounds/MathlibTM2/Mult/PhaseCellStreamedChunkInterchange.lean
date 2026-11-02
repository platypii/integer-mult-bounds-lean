module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDimensionRowScope
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkInterchange

/-! One fixed physical stage reads its five dimensions from a binary schedule
row, runs the generated interchange and releases the reusable unary masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def interchangeDimensionRow {T : ℕ} (dims : Fin 5 → Fin T) (P B h d : ℕ) : List (ℕ × Fin T) :=
  List.ofFn fun k => (swapValues P 1 B h d k,dims k)

theorem interchangeDimensionRow_lifecycleCost {T : ℕ} (dims : Fin 5 → Fin T)
    (V P B h d : ℕ) :
    let row := interchangeDimensionRow dims P B h d
    readDimensionRowCost V row+(2*(row.map Prod.fst).sum+2*row.length+1) =
      95*V+14*(P+1+B+h+d)+132 := by
  simp [interchangeDimensionRow,readDimensionRowCost,readUnaryDimensionCost,List.ofFn_succ,swapValues]
  ring

noncomputable def streamedChunkInterchange {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (width zero queue binary duplicate readerWork saved tmp : Fin T)
    (a half par bits cnt work : Fin T) : Pr P T Q (prime+K) U :=
  withDimensionRow width zero queue binary duplicate readerWork saved tmp (List.ofFn dims)
    (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work)

theorem streamedChunkInterchange_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (hdims : Function.Injective dims)
    (width zero queue binary duplicate readerWork saved tmp a half par bits cnt work : Fin T)
    (hreader : ∀ k, [width,zero,queue,binary,dims k,duplicate,readerWork,saved,tmp].Nodup)
    (hgen : ∀ k, [dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdimOff : ∀ k j, dims k ≠ ι j) (hqueueOff : ∀ j, queue ≠ ι j)
    (hqueueControls : ∀ i ∈ [a,half,par,bits,cnt,work], queue ≠ i)
    (V outerCount blockWidth h d : ℕ) (hfit : ∀ k, swapValues outerCount 1 blockWidth h d k < 2^V)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1) (houter : 0 < outerCount) (hblock : 0 < blockWidth)
    (xs : List Bool) (hlen : xs.length = BinaryAdjacentWidthInterchange.volume outerCount (2^h) 1 (2^d) blockWidth)
    (tail : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = ((interchangeDimensionRow dims outerCount blockWidth h d).flatMap
      fun p => binSyms V p.1)++tail)
    (hblank : ∀ i ∈ [binary,duplicate,readerWork,saved,tmp]++List.ofFn dims, S.R i = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let row := interchangeDimensionRow dims outerCount blockWidth h d
    ∃ v' n, v'.user = v.user ∧
      n ≤ readDimensionRowCost V row+
        generatedBalancedChunkInterchangeCost T t₀ outerCount blockWidth h d (∑ j, (S.R (ι j)).length)+
        (2*(row.map Prod.fst).sum+2*row.length+1) ∧
      Exec body (streamedChunkInterchange hd pay hi hQ ι hι hT dims width zero queue binary duplicate
        readerWork saved tmp a half par bits cnt work) (Host.mk v S) n
        (Host.mk v' {S with L := fun _ => [], R := (Function.update (Function.update S.R queue tail)
          (ι (reg pay)) ((swapList outerCount (2^h) 1 (2^d) blockWidth false xs).map bitSymbol))}) := by
  let row := interchangeDimensionRow dims outerCount blockWidth h d
  have hports : row.map Prod.snd = List.ofFn dims := by simp [row,interchangeDimensionRow,List.map_ofFn]
  have hds : (row.map Prod.snd).Nodup := hports ▸ List.nodup_ofFn_ofInjective hdims
  let M := dimensionRowState row queue tail S
  have hframe (i : Fin T) (hd : ∀ k, dims k ≠ i) (hq : queue ≠ i) : M.R i = S.R i := by
    dsimp only [M,dimensionRowState]
    rw [dimensionRowR_off row _ i (by
      intro p hp
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
      exact hd k)]
    exact Function.update_of_ne hq.symm _ _
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) :=
    hframe _ (fun k => hdimOff k j) (hqueueOff j)
  have hrun : ∀ vi : HS T Q (prime+K) U, ∃ vf n, vf.user = vi.user ∧
      n ≤ generatedBalancedChunkInterchangeCost T t₀ outerCount blockWidth h d (∑ j, (S.R (ι j)).length) ∧
      Exec body (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work)
        (Host.mk vi M) n (Host.mk vf {M with L := fun _ => [], R := (Function.update M.R (ι (reg pay))
          ((swapList outerCount (2^h) 1 (2^d) blockWidth false xs).map bitSymbol))}) := by
    intro vi
    obtain ⟨vf,n,hu,hn,he⟩ := generatedBalancedChunkInterchange_exec body hd pay hi hpay hQ ι hι hT
      dims a half par bits cnt work hgen (fun k j => (hdimOff j (reg (hd k))).symm)
      outerCount blockWidth h d hhd hdh houter hblock xs hlen vi M hL
      (by intro j hj; rw [hbank]; exact hpriv j hj)
      (by
        intro k
        change (dimensionRowR row (Function.update S.R queue tail) (dims k)).length = _
        rw [dimensionRowR_at row _ hds (swapValues outerCount 1 blockWidth h d k,dims k)
          (List.mem_ofFn.mpr ⟨k,rfl⟩),List.length_replicate])
      (by intro k; rw [hbank]; exact hhdr k)
      (by
        intro i hi
        rw [hframe i (by
          intro k he
          apply (List.nodup_cons.mp (hgen k)).1
          rw [he]
          exact List.mem_cons_of_mem _ hi) (hqueueControls i hi)]
        exact hgenBlank i hi)
      (by rw [hbank]; exact hsrc)
      (by intro i hip hheads s hs; rw [hbank] at hs; exact hother i hip hheads s hs)
    refine ⟨vf,n,hu,?_,he⟩
    simpa only [hbank] using hn
  have he := withDimensionRow_exec width zero queue binary duplicate readerWork saved tmp (ι (reg pay))
    V row (by intro p hp; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp; exact hreader k) hds
    (by intro p hp; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp; exact hfit k)
    (by intro p hp; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp; exact hdimOff k (reg pay))
    (by
      intro p hp
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
      have hr := hreader k
      regs_ne hr
      exact Ne.symm (by assumption))
    tail ((swapList outerCount (2^h) 1 (2^d) blockWidth false xs).map bitSymbol)
    (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work) _ v S hwidth hzero hqueue
    (by simpa only [hports] using hblank) hrun
  simpa only [streamedChunkInterchange,hports] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
