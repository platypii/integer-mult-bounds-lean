module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkStageWiring

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def generatedChunkTile {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (base one width tmp saved a half par bits cnt work : Fin T)
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) : Pr P T Q (prime+K) U :=
  .seq (chunkDimensionBank base one width tmp saved ps bs)
    (.seq (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
      (releaseChunkDimensionBank ps bs))

noncomputable def generatedChunkTileCost (T t₀ d W stock : ℕ)
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) : ℕ :=
  (unaryPowerChainCost (2^d) 1 ps.length+unaryPowerChainCost (2^d) W bs.length)+
    (((rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d stock)).sum+1)+
      ((2*unaryPowerChainVolume (2^d) W bs.length+2*bs.length+1)+
        (2*unaryPowerChainVolume (2^d) 1 ps.length+2*ps.length+1)))

theorem generatedChunkTileCost_mono {T t₀ d W stock stock' : ℕ}
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) (hstock : stock ≤ stock') :
    generatedChunkTileCost T t₀ d W stock ps bs rs ≤ generatedChunkTileCost T t₀ d W stock' ps bs rs := by
  have hh : (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d stock)).sum ≤
      (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d stock')).sum := by
    apply List.sum_le_sum
    intro r hr
    dsimp only [generatedChunkInterchangeCost]
    omega
  dsimp only [generatedChunkTileCost]
  exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right hh 1) _) _

theorem generatedChunkTileCost_reverse (T t₀ d W stock : ℕ)
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) :
    generatedChunkTileCost T t₀ d W stock ps bs rs.reverse = generatedChunkTileCost T t₀ d W stock ps bs rs := by
  simp only [generatedChunkTileCost,List.map_reverse,List.sum_reverse]

/-- Generate both dimension banks, execute every chunk stage with derived
readiness, and dispose of both banks. Only the bit payload changes. -/
theorem generatedChunkTileUsing_exec {t₀ T Q K c : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (base one width exponent tmp saved a half par bits cnt work : Fin T)
    (ps bs : List (Fin T))
    (hp : ([base,tmp,saved,one]++ps).Nodup) (hb : ([base,tmp,saved,width]++bs).Nodup)
    (hsep : ∀ p ∈ one::ps, ∀ b ∈ width::bs, p ≠ b)
    (hbankOff : ∀ i ∈ ps++bs, ∀ j, i ≠ ι j)
    (hprotected : ∀ i ∈ [a,half,par,bits,cnt,work,exponent], i ∉ ps++bs)
    (prefixes suffixes : Fin c → Fin T)
    (hprefixes : List.ofFn prefixes = one::ps) (hsuffixes : List.ofFn suffixes = width::bs)
    (d W : ℕ) (hW : 0 < W) (rs : List (ChunkInterchangeStage T))
    (hstage : ∀ r ∈ rs, r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes)
    (hgen : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, r.dims k ≠ ι (reg pay))
    (hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg pay))
    (xs : List Bool) (hlen : xs.length = (2^d)^c*(2^d)*W)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (generatedChunkTile hd pay hi hQ ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((chunkStageBits d rs xs).map bitSymbol)}) := by
  dsimp only [generatedChunkTileCost]
  let forward := wiredChunkStages (2^d) W one exponent prefixes suffixes
  have hps : (one::ps).Nodup := (show ([base,tmp,saved]++(one::ps)).Nodup from hp).of_append_right
  have hbs : (width::bs).Nodup := (show ([base,tmp,saved]++(width::bs)).Nodup from hb).of_append_right
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := chunkDimensionBank_exec base one width tmp saved ps bs hp hb
    (by intro p hp; exact hsep p (by simp [hp])) (2^d) W v S hbase hone hwidth hblank htmp hsaved
  let M : Stacks T (prime+K) := {S with R := chunkDimensionBankR (2^d) W ps bs S.R}
  have hframe (i : Fin T) (hi : i ∉ ps++bs) : M.R i = S.R i := chunkDimensionBankR_off _ _ _ _ _ _ hi
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) :=
    hframe _ (by intro hi; exact hbankOff _ hi j rfl)
  have hstock : (∑ j, (M.R (ι j)).length) = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbank]
  have hshape := wiredChunkStages_shape (2^d) W one exponent prefixes suffixes
  have hready := chunkStages_shape_ready d W c hW forward hshape
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := chunkInterchangeLoop_exec body hd pay hi hpay hQ ι hι hT
    a half par bits cnt work d ((2^d)^c*(2^d)*W) rs
    (by intro r hr; exact hgen r (hstage r hr))
    (by intro r hr; exact hdisjoint r (hstage r hr))
    (by intro r hr; exact hmaster r (hstage r hr)) hscratch
    (by intro r hr; exact (hready r (hstage r hr)).1) (by intro r hr; exact (hready r (hstage r hr)).2)
    xs hlen v₁ M hL
    (by intro j hj; rw [hbank]; exact hpriv j hj)
    (by
      intro r hr k
      exact wiredChunkStages_bank_values d W one width exponent ps bs hps hbs hsep prefixes suffixes
        hprefixes hsuffixes (hprotected exponent (by simp)) S.R hone hwidth hexponent r (hstage r hr) k)
    (by intro k; rw [hbank]; exact hhdr k)
    (by intro i hi; rw [hframe i (hprotected i (List.mem_append_left [exponent] hi))]; exact hgenBlank i hi)
    (by rw [hbank]; exact hsrc)
    (by intro i hip hheads s hs; rw [hbank] at hs; exact hother i hip hheads s hs)
  rw [hstock] at hn₂
  let D : Stacks T (prime+K) := {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((chunkStageBits d rs xs).map bitSymbol)}
  have hsrcOff : ι (reg pay) ∉ ps++bs := by intro hi; exact hbankOff _ hi (reg pay) rfl
  have he₂' : Exec body (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
      (mk v₁ M) n₂ (mk v₂ {D with R := chunkDimensionBankR (2^d) W ps bs D.R}) := by
    refine he₂.cast rfl ?_
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    exact (chunkDimensionBankR_update_off _ _ _ _ S.R _ _ hsrcOff).symm
  obtain ⟨v₃,hu₃,he₃⟩ := releaseChunkDimensionBank_exec (2^d) W ps bs
    (List.nodup_cons.mp hps).2 (List.nodup_cons.mp hbs).2
    (by intro p hp b hb; exact hsep p (by simp [hp]) b (by simp [hb])) v₂ D (by
      intro i hi
      rw [show D.R i = S.R i from Function.update_of_ne (hbankOff i hi (reg pay)) _ _]
      exact hblank i hi)
  refine ⟨v₃,n₁+(n₂+((2*unaryPowerChainVolume (2^d) W bs.length+2*bs.length+1)+
    (2*unaryPowerChainVolume (2^d) 1 ps.length+2*ps.length+1))),
    hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)


/-- Generate both dimension banks, execute every chunk stage with derived
readiness, and dispose of both banks. Only the bit payload changes. -/
theorem generatedChunkTile_exec {t₀ T Q K c : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (base one width exponent tmp saved a half par bits cnt work : Fin T)
    (ps bs : List (Fin T))
    (hp : ([base,tmp,saved,one]++ps).Nodup) (hb : ([base,tmp,saved,width]++bs).Nodup)
    (hsep : ∀ p ∈ one::ps, ∀ b ∈ width::bs, p ≠ b)
    (hbankOff : ∀ i ∈ ps++bs, ∀ j, i ≠ ι j)
    (hprotected : ∀ i ∈ [a,half,par,bits,cnt,work,exponent], i ∉ ps++bs)
    (prefixes suffixes : Fin c → Fin T)
    (hprefixes : List.ofFn prefixes = one::ps) (hsuffixes : List.ofFn suffixes = width::bs)
    (d W : ℕ) (hW : 0 < W)
    (hgen : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, r.dims k ≠ ι (reg pay))
    (hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg pay))
    (f : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = (replicaKeyWords f).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (generatedChunkTile hd pay hi hQ ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((keyReplicaWords f).map bitSymbol)}) := by
  dsimp only
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  obtain ⟨v',n,hu,hn,he⟩ := generatedChunkTileUsing_exec body hd pay hi hpay hQ ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs (by intro r hr; exact hr)
    hgen hdisjoint hmaster hscratch (replicaKeyWords f) (by simp [replicaKeyWords,Nat.mul_assoc])
    v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hsrc hother
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [chunkStageBits_words d W c rs (wiredChunkStages_shape _ _ _ _ _ _) f] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
