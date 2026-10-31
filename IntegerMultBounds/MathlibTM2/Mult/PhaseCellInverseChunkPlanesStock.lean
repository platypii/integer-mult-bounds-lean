module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkPlanesStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem generatedChunkPlanes_inverse_exec_within {t₀ T Q K c : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hne : re ≠ im) (hreHead : ∀ k, hd k ≠ re) (himHead : ∀ k, hd k ≠ im)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
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
      ∀ k, r.dims k ≠ ι (reg re) ∧ r.dims k ≠ ι (reg im))
    (hcontrols : ∀ i ∈ [base,one,width,exponent,tmp,saved,a,half,par,bits,cnt,work],
      i ≠ ι (reg re) ∧ i ≠ ι (reg im))
    (realBits imagBits : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hre : S.R (ι (reg re)) = (keyReplicaWords realBits).map bitSymbol)
    (him : S.R (ι (reg im)) = (keyReplicaWords imagBits).map bitSymbol)
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2*generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*(unaryPowerChainCost (2^d) 1 ps.length+unaryPowerChainCost (2^d) W bs.length)+
          chunkStockAllowance T d rs.reverse) depth (generatedChunkPlanes hd re im hi hQre hQim ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs.reverse) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update
          (Function.update S.R (ι (reg re)) ((replicaKeyWords realBits).map bitSymbol))
            (ι (reg im)) ((replicaKeyWords imagBits).map bitSymbol))}) := by
  dsimp only
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  have he := generatedChunkPlanesUsing_exec_within body hd re im hi hne hreHead himHead hQre hQim ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs.reverse (by intro r hr; exact List.mem_reverse.mp hr)
    hgen hdisjoint hmaster hcontrols (keyReplicaWords realBits) (keyReplicaWords imagBits)
    (by simp [keyReplicaWords,replicaKeyWords,Nat.mul_comm,Nat.mul_left_comm])
    (by simp [keyReplicaWords,replicaKeyWords,Nat.mul_comm,Nat.mul_left_comm])
    v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hre him hother depth
  simpa only [generatedChunkTileCost_reverse,
    chunkStageBits_reverse_words d W c rs (wiredChunkStages_shape _ _ _ _ _ _) realBits,
    chunkStageBits_reverse_words d W c rs (wiredChunkStages_shape _ _ _ _ _ _) imagBits] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
