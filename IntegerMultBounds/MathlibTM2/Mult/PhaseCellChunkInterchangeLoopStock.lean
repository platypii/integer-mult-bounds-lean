module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBalancedChunkInterchangeLoopStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Chronological chunk stages share one reserve: each stage restores scratch
and preserves the length of the only changed payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def chunkStageStockAllowance {T : ℕ} (t d : ℕ) (r : ChunkInterchangeStage T) : ℕ :=
  2*(21*(r.outerCount+1+r.blockWidth+d+d)+56)+
    t*(2*SwapMachineStock.reserve r.outerCount 1 r.blockWidth d d+2)+3*t+20

noncomputable def chunkStockAllowance {T : ℕ} (t d : ℕ) : List (ChunkInterchangeStage T) → ℕ
  | [] => 0
  | r::rs => max (chunkStageStockAllowance t d r) (chunkStockAllowance t d rs)

theorem balancedChunkStockAllowance_equalWidth {T : ℕ} (t d : ℕ)
    (rs : List (ChunkInterchangeStage T)) :
    balancedChunkStockAllowance t (rs.map (ChunkInterchangeStage.balanced d)) =
      chunkStockAllowance t d rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,balancedChunkStockAllowance,chunkStockAllowance,
      balancedChunkStageStockAllowance,chunkStageStockAllowance,ChunkInterchangeStage.balanced,ih]

theorem chunkInterchangeLoop_exec_within {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) (d V : ℕ) (rs : List (ChunkInterchangeStage T))
    (hgen : ∀ r ∈ rs, ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ rs, ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ rs, ∀ k, r.dims k ≠ ι (reg pay))
    (hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg pay))
    (hpositive : ∀ r ∈ rs, 0 < r.outerCount ∧ 0 < r.blockWidth)
    (hvolume : ∀ r ∈ rs, V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth)
    (xs : List Bool) (hlen : xs.length = V)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ r ∈ rs, ∀ k, (S.R (r.dims k)).length = swapValues r.outerCount 1 r.blockWidth d d k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d
        (∑ j, (S.R (ι j)).length))).sum+1 ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        chunkStockAllowance T d rs) depth (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((chunkStageBits d rs xs).map bitSymbol))}) := by
  simpa only [balancedChunkInterchangeLoop_equalWidth,balancedChunkStageBits_equalWidth,
    balancedChunkStockAllowance_equalWidth,List.map_map,Function.comp_def,
    ChunkInterchangeStage.balanced,generatedBalancedChunkInterchangeCost,
    generatedChunkInterchangeCost] using
    balancedChunkInterchangeLoop_exec_within body hd pay hi hpay hQ ι hι hT a half par bits cnt work
      V (rs.map (ChunkInterchangeStage.balanced d))
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hgen s hs)
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hdisjoint s hs)
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hmaster s hs)
      hscratch
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hpositive s hs)
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact ⟨Nat.le_succ d,Nat.le_succ d⟩)
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hvolume s hs)
      xs hlen v S hL hpriv
      (by intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr; exact hdims s hs)
      hhdr hgenBlank hsrc hother depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
