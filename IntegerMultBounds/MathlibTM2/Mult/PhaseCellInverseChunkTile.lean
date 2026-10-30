module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkTile

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Restore replica order by executing the existing generated tile stages in
reverse order. The bank lifecycle and exact bill are shared with forward routing. -/
theorem generatedChunkTile_inverse_exec {t₀ T Q K c : ℕ} {U P : Type}
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
    (hsrc : S.R (ι (reg pay)) = (keyReplicaWords f).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (generatedChunkTile hd pay hi hQ ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs.reverse) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) ((replicaKeyWords f).map bitSymbol)}) := by
  dsimp only
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  obtain ⟨v',n,hu,hn,he⟩ := generatedChunkTileUsing_exec body hd pay hi hpay hQ ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs.reverse (by intro r hr; exact List.mem_reverse.mp hr)
    hgen hdisjoint hmaster hscratch (keyReplicaWords f)
    (by simp [keyReplicaWords,replicaKeyWords,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm])
    v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hsrc hother
  rw [generatedChunkTileCost_reverse] at hn
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [chunkStageBits_reverse_words d W c rs (wiredChunkStages_shape _ _ _ _ _ _) f] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
