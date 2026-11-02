module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBalancedChunkInterchangeLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaChunkInverse

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- A stage selects borrowed dimension masters and records its mathematical shape.
The program reads the masters; it does not bake their values into its code. -/
structure ChunkInterchangeStage (T : ℕ) where
  dims : Fin 5 → Fin T
  outerCount : ℕ
  blockWidth : ℕ

def chunkStageBits {T : ℕ} (d : ℕ) : List (ChunkInterchangeStage T) → List Bool → List Bool
  | [],xs => xs
  | r::rs,xs => chunkStageBits d rs (swapList r.outerCount (2^d) 1 (2^d) r.blockWidth false xs)

theorem chunkStageBits_eq {T : ℕ} (d : ℕ) (rs : List (ChunkInterchangeStage T)) (xs : List Bool) :
    chunkStageBits d rs xs = runReplicaChunkSwaps (2^d) false
      (rs.map fun r => (r.outerCount,r.blockWidth)) xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem chunkStageBits_length {T : ℕ} (d : ℕ) (rs : List (ChunkInterchangeStage T))
    (V : ℕ) (hvolume : ∀ r ∈ rs,
      V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth)
    (xs : List Bool) (hlen : xs.length = V) : (chunkStageBits d rs xs).length = V := by
  rw [chunkStageBits_eq]
  apply runReplicaChunkSwaps_length (2^d) false _ V _ xs hlen
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using (hvolume s hs).symm

/-- The actual loop's payload description agrees with the complete-key layout
when its stage shapes follow the structural chunk schedule. -/
theorem chunkStageBits_words {T : ℕ} (d W c : ℕ) (rs : List (ChunkInterchangeStage T))
    (hshape : (rs.map fun r => (r.outerCount,r.blockWidth)) = replicaChunkSwaps (2^d) W c)
    (f : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool) :
    chunkStageBits d rs (replicaKeyWords f) = keyReplicaWords f := by
  rw [chunkStageBits_eq,hshape]
  exact runReplicaChunkSwaps_words (2^d) W c false f

theorem chunkStageBits_reverse_words {T : ℕ} (d W c : ℕ) (rs : List (ChunkInterchangeStage T))
    (hshape : (rs.map fun r => (r.outerCount,r.blockWidth)) = replicaChunkSwaps (2^d) W c)
    (f : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool) :
    chunkStageBits d rs.reverse (keyReplicaWords f) = replicaKeyWords f := by
  rw [chunkStageBits_eq,List.map_reverse,hshape]
  exact runReplicaChunkSwaps_inverse_words (2^d) W c false f

/-- The structural schedule supplies the positivity and common-volume premises
of every machine stage; these are not separate per-stage certificates. -/
theorem chunkStages_shape_ready {T : ℕ} (d W c : ℕ) (hW : 0 < W)
    (rs : List (ChunkInterchangeStage T))
    (hshape : (rs.map fun r => (r.outerCount,r.blockWidth)) = replicaChunkSwaps (2^d) W c) :
    ∀ r ∈ rs, (0 < r.outerCount ∧ 0 < r.blockWidth) ∧
      (2^d)^c*(2^d)*W = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth := by
  intro r hr
  have hm : (r.outerCount,r.blockWidth) ∈ replicaChunkSwaps (2^d) W c := by
    rw [←hshape]
    exact List.mem_map.mpr ⟨r,hr,rfl⟩
  refine ⟨replicaChunkSwaps_positive (pow_pos (by decide : 0 < 2) d) hW c _ hm,?_⟩
  simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using
    (replicaChunkSwaps_stage_volume (2^d) W c _ hm).symm

noncomputable def chunkInterchangeLoop {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) : List (ChunkInterchangeStage T) → Pr P T Q (prime+K) U
  | [] => .act .done
  | r::rs => .seq (generatedChunkInterchange hd pay hi hQ ι hι hT r.dims a half par bits cnt work)
      (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)

/-- View the existing equal-width schedule as a balanced schedule. -/
def ChunkInterchangeStage.balanced {T : ℕ} (d : ℕ)
    (r : ChunkInterchangeStage T) : BalancedChunkInterchangeStage T :=
  ⟨r.dims,r.outerCount,r.blockWidth,d,d⟩

theorem balancedChunkStageBits_equalWidth {T : ℕ} (d : ℕ)
    (rs : List (ChunkInterchangeStage T)) (xs : List Bool) :
    balancedChunkStageBits (rs.map (ChunkInterchangeStage.balanced d)) xs = chunkStageBits d rs xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem balancedChunkInterchangeLoop_equalWidth {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) (d : ℕ) (rs : List (ChunkInterchangeStage T)) :
    balancedChunkInterchangeLoop (K := K) (U := U) (P := P) hd pay hi hQ ι hι hT
      a half par bits cnt work (rs.map (ChunkInterchangeStage.balanced d)) =
      chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,balancedChunkInterchangeLoop,chunkInterchangeLoop,
      ChunkInterchangeStage.balanced]
    rw [ih]

theorem chunkInterchangeLoop_exec {t₀ T Q K : ℕ} {U P : Type}
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
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d
        (∑ j, (S.R (ι j)).length))).sum+1 ∧
      Exec body (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((chunkStageBits d rs xs).map bitSymbol))}) := by
  simpa only [balancedChunkInterchangeLoop_equalWidth,balancedChunkStageBits_equalWidth,
    List.map_map,Function.comp_def,ChunkInterchangeStage.balanced,
    generatedBalancedChunkInterchangeCost,generatedChunkInterchangeCost] using
    balancedChunkInterchangeLoop_exec body hd pay hi hpay hQ ι hι hT a half par bits cnt work
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
      hhdr hgenBlank hsrc hother

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
