module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Actual dimension-bank allocation, chronological interchange and release
share the loop reserve and pay the linear native allocation once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem generatedChunkTileUsing_exec_within {t₀ T Q K c : ℕ} {U P : Type}
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
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        2*(unaryPowerChainCost (2^d) 1 ps.length+unaryPowerChainCost (2^d) W bs.length)+
        chunkStockAllowance T d rs) depth (generatedChunkTile hd pay hi hQ ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((chunkStageBits d rs xs).map bitSymbol)}) := by
  let forward := wiredChunkStages (2^d) W one exponent prefixes suffixes
  have hps : (one::ps).Nodup := (show ([base,tmp,saved]++(one::ps)).Nodup from hp).of_append_right
  have hbs : (width::bs).Nodup := (show ([base,tmp,saved]++(width::bs)).Nodup from hb).of_append_right
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := chunkDimensionBank_exec (body := body) base one width tmp saved ps bs hp hb
    (by intro p hp; exact hsep p (by simp [hp])) (2^d) W v S hbase hone hwidth hblank htmp hsaved
  let setup := 2*(unaryPowerChainCost (2^d) 1 ps.length+unaryPowerChainCost (2^d) W bs.length)
  let extra := chunkStockAllowance T d rs
  let bound := mnSize (mk v S)+depth+setup+extra
  have hw₁ := mn_native_exec_within he₁ 2 (chunkDimensionBank_native base one width tmp saved ps bs)
    depth (mnSize (mk v S)+depth+setup) (by dsimp only [setup]; omega)
  have hsetup := hw₁.final
  have hw₁' := hw₁.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    exact hc.trans (Nat.le_add_right _ _))
  let M : Stacks T (prime+K) := {S with R := chunkDimensionBankR (2^d) W ps bs S.R}
  have hframe (i : Fin T) (hi : i ∉ ps++bs) : M.R i = S.R i := chunkDimensionBankR_off _ _ _ _ _ _ hi
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) :=
    hframe _ (by intro hi; exact hbankOff _ hi j rfl)
  have hshape := wiredChunkStages_shape (2^d) W one exponent prefixes suffixes
  have hready := chunkStages_shape_ready d W c hW forward hshape
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := chunkInterchangeLoop_exec_within body hd pay hi hpay hQ ι hι hT
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
    (by intro i hip hheads s hs; rw [hbank] at hs; exact hother i hip hheads s hs) depth
  change mnSize (mk v₁ M)+depth ≤ mnSize (mk v S)+depth+setup at hsetup
  have hw₂ := he₂.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    change mnSize c+z ≤ mnSize (mk v₁ M)+depth+extra at hc
    exact hc.trans (Nat.add_le_add_right hsetup extra))
  let D : Stacks T (prime+K) := {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((chunkStageBits d rs xs).map bitSymbol)}
  have hsrcOff : ι (reg pay) ∉ ps++bs := by intro hi; exact hbankOff _ hi (reg pay) rfl
  have he₂' : ExecWithin body (fun z c => mnSize c+z ≤ bound) depth (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
      (mk v₁ M) n₂ (mk v₂ {D with R := chunkDimensionBankR (2^d) W ps bs D.R}) := by
    have hout : mk v₂ {M with L := fun _ => [], R := (Function.update M.R (ι (reg pay))
        ((chunkStageBits d rs xs).map bitSymbol))} =
        mk v₂ {D with R := chunkDimensionBankR (2^d) W ps bs D.R} := by
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      exact (chunkDimensionBankR_update_off _ _ _ _ S.R _ _ hsrcOff).symm
    exact (congrArg (fun f => ExecWithin body (fun z c => mnSize c+z ≤ bound) depth
      (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs) (mk v₁ M) n₂ f) hout).mp hw₂
  obtain ⟨v₃,hu₃,he₃⟩ := releaseChunkDimensionBank_exec (body := body) (2^d) W ps bs
    (List.nodup_cons.mp hps).2 (List.nodup_cons.mp hbs).2
    (by intro p hp b hb; exact hsep p (by simp [hp]) b (by simp [hb])) v₂ D (by
      intro i hi
      rw [show D.R i = S.R i from Function.update_of_ne (hbankOff i hi (reg pay)) _ _]
      exact hblank i hi)
  have hw₃ := mn_native_exec_within he₃ 0 (releaseChunkDimensionBank_native ps bs)
    depth bound (by have hh := he₂'.final; simpa only [Nat.zero_mul,Nat.add_zero] using hh)
  have hwhole := ExecWithin.seq hw₁' (ExecWithin.seq he₂' hw₃)
  change ExecWithin body _ depth
    (generatedChunkTile hd pay hi hQ ι hι hT base one width tmp saved a half par bits cnt work ps bs rs)
    (mk v S) _ _ at hwhole
  obtain ⟨vf,n,hu,hn,he⟩ := generatedChunkTileUsing_exec body hd pay hi hpay hQ ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs hstage hgen hdisjoint hmaster hscratch
    xs hlen v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hsrc hother
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique he
  rw [hsteps,hfinal] at hwhole
  exact ⟨vf,n,hu,hn,hwhole⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
