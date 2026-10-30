module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkTile

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem encodedBits_good {K : ℕ} (xs : List Bool) (s : Fin (prime+K+4))
    (hs : s ∈ xs.map bitSymbol) : s ≠ blank ∧ s.val < prime+4 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  exact bitSymbol_good b

noncomputable def generatedChunkPlanes {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (base one width tmp saved a half par bits cnt work : Fin T)
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) : Pr P T Q (prime+K) U :=
  .seq (generatedChunkTile hd re hi hQre ι hι hT base one width tmp saved a half par bits cnt work ps bs rs)
    (generatedChunkTile hd im hi hQim ι hι hT base one width tmp saved a half par bits cnt work ps bs rs)

/-- Reuse the restored tile lifecycle for both physical bit planes. The second
call receives all readiness and the same bank volume from the first call. -/
theorem generatedChunkPlanesUsing_exec {t₀ T Q K c : ℕ} {U P : Type}
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
    (rs : List (ChunkInterchangeStage T))
    (hstage : ∀ r ∈ rs, r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes)
    (hgen : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, r.dims k ≠ ι (reg re) ∧ r.dims k ≠ ι (reg im))
    (hcontrols : ∀ i ∈ [base,one,width,exponent,tmp,saved,a,half,par,bits,cnt,work],
      i ≠ ι (reg re) ∧ i ≠ ι (reg im))
    (realBits imagBits : List Bool)
    (hreLen : realBits.length = (2^d)^c*(2^d)*W)
    (himLen : imagBits.length = (2^d)^c*(2^d)*W)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hre : S.R (ι (reg re)) = realBits.map bitSymbol)
    (him : S.R (ι (reg im)) = imagBits.map bitSymbol)
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2*generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (generatedChunkPlanes hd re im hi hQre hQim ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update
          (Function.update S.R (ι (reg re)) ((chunkStageBits d rs realBits).map bitSymbol))
            (ι (reg im)) ((chunkStageBits d rs imagBits).map bitSymbol))}) := by
  have hplaced : Function.Injective (fun i : Fin t₀ => ι (reg i)) := hι.comp swapReg_injective
  have hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg re) ∧ i ≠ ι (reg im) := by
    intro i hi
    apply hcontrols
    exact List.mem_append_right [base,one,width,exponent,tmp,saved] hi
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedChunkTileUsing_exec body hd re hi hreHead hQre ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs hstage hgen hdisjoint
    (by intro r hr k; exact (hmaster r hr k).1) (by intro i hi; exact (hscratch i hi).1)
    realBits hreLen v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hre (by
      intro i hire hheads s hs
      by_cases hiim : i = im
      · subst i; rw [him] at hs; exact encodedBits_good _ s hs
      · exact hother i hire hiim hheads s hs)
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update S.R (ι (reg re))
    ((chunkStageBits d rs realBits).map bitSymbol))}
  have hframe (i : Fin T) (hi : i ≠ ι (reg re)) : M.R i = S.R i := Function.update_of_ne hi _ _
  have hcontrolFrame (i : Fin T) (hi : i ∈ [base,one,width,exponent,tmp,saved,a,half,par,bits,cnt,work]) :
      M.R i = S.R i := hframe i (hcontrols i hi).1
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedChunkTileUsing_exec body hd im hi himHead hQim ι hι hT
    base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
    prefixes suffixes hprefixes hsuffixes d W hW rs hstage hgen hdisjoint
    (by intro r hr k; exact (hmaster r hr k).2) (by intro i hi; exact (hscratch i hi).2)
    imagBits himLen v₁ M
    (by rw [hcontrolFrame base (by simp)]; exact hbase)
    (by rw [hcontrolFrame one (by simp)]; exact hone)
    (by rw [hcontrolFrame width (by simp)]; exact hwidth)
    (by rw [hcontrolFrame exponent (by simp)]; exact hexponent)
    (by intro i hi; rw [hframe i (hbankOff i hi (reg re))]; exact hblank i hi)
    (by rw [hcontrolFrame tmp (by simp)]; exact htmp)
    (by rw [hcontrolFrame saved (by simp)]; exact hsaved)
    (by intro i; rfl)
    (by
      intro j hj
      rw [hframe]
      · exact hpriv j hj
      · intro he
        have hh := congrArg Fin.val (hι he)
        change j.val = re.val at hh
        have hr := re.isLt
        omega)
    (by intro k; rw [hframe _ (hplaced.ne (hreHead k))]; exact hhdr k)
    (by intro i hi; rw [hframe i (hscratch i hi).1]; exact hgenBlank i hi)
    (by rw [hframe _ (hplaced.ne hne.symm)]; exact him)
    (by
      intro i hiim hheads s hs
      by_cases hire : i = re
      · subst i
        simp only [M,Function.update_self] at hs
        exact encodedBits_good _ s hs
      · rw [hframe _ (hplaced.ne hire)] at hs
        exact hother i hire hiim hheads s hs)
  have hlength : ((chunkStageBits d rs realBits).map (bitSymbol (a := prime+K))).length =
      (S.R (ι (reg re))).length := by
    rw [hre]
    simp only [List.length_map]
    rw [hreLen]
    exact chunkStageBits_length d rs _ (by
      intro r hr
      exact (chunkStages_shape_ready d W c hW _
        (wiredChunkStages_shape _ _ _ _ _ _) r (hstage r hr)).2) realBits hreLen
  have hvolume : (∑ j, (M.R (ι j)).length) = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : ι j = ι (reg re)
    · simpa only [M,he,Function.update_self] using hlength
    · rw [hframe _ he]
  rw [hvolume] at hn₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  simpa only [two_mul] using Nat.add_le_add hn₁ hn₂

theorem generatedChunkPlanes_exec {t₀ T Q K c : ℕ} {U P : Type}
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
    (hre : S.R (ι (reg re)) = (replicaKeyWords realBits).map bitSymbol)
    (him : S.R (ι (reg im)) = (replicaKeyWords imagBits).map bitSymbol)
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ 2*generatedChunkTileCost T t₀ d W (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (generatedChunkPlanes hd re im hi hQre hQim ι hι hT base one width tmp saved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update
          (Function.update S.R (ι (reg re)) ((keyReplicaWords realBits).map bitSymbol))
            (ι (reg im)) ((keyReplicaWords imagBits).map bitSymbol))}) := by
  dsimp only
  simpa only [chunkStageBits_words d W c _ (wiredChunkStages_shape _ _ _ _ _ _) realBits,
    chunkStageBits_words d W c _ (wiredChunkStages_shape _ _ _ _ _ _) imagBits] using
    generatedChunkPlanesUsing_exec body hd re im hi hne hreHead himHead hQre hQim ι hι hT
      base one width exponent tmp saved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
      prefixes suffixes hprefixes hsuffixes d W hW
      (wiredChunkStages (2^d) W one exponent prefixes suffixes) (by intros; assumption)
      hgen hdisjoint hmaster hcontrols (replicaKeyWords realBits) (replicaKeyWords imagBits)
      (by simp [replicaKeyWords,Nat.mul_assoc]) (by simp [replicaKeyWords,Nat.mul_assoc])
      v S hbase hone hwidth hexponent hblank htmp hsaved hL hpriv hhdr hgenBlank hre him hother

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
