module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPackedGeneratedChunkTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratedChunkTileStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPayloadStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Count the actual packed tile, execute both generated routes and the codec,
and restore the initially blank counter. Only the packed payload changes. -/
theorem countedPackedGeneratedChunkTile_exec_within {t₀ T Q K c : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hne : re ≠ im) (hreHead : ∀ k, hd k ≠ re) (himHead : ∀ k, hd k ≠ im)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T)
    (hreg : [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev].Nodup)
    (base one width exponent powTmp powSaved a half par bits cnt work : Fin T)
    (ps bs : List (Fin T))
    (hp : ([base,powTmp,powSaved,one]++ps).Nodup) (hb : ([base,powTmp,powSaved,width]++bs).Nodup)
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
    (hcontrols : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work],
      i ≠ ι (reg re) ∧ i ≠ ι (reg im))
    (realBits imagBits : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R powTmp = []) (hsaved : S.R powSaved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))
    (hcount : S.R count = [])
    (hcodecBlank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hcountOff : ∀ j, ι j ≠ count)
    (hcountControls : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work], i ≠ count)
    (hcountBank : count ∉ ps++bs)
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ countedPackedGeneratedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*(4*((2^d)^c*(2^d*W))+4)+packedChunkStockAllowance T d W c ps bs rs)
        depth (countedPackedGeneratedChunkTile hd re im hi hQre hQim ι hι hT
        src tmp saved count reRev imRev base one width powTmp powSaved
        a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update S.R src
          (keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b))))}) := by
  dsimp only [countedPackedGeneratedChunkTileCost]
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  let V := (2^d)^c*(2^d*W)
  have hr := hreg
  regs_ne hr
  have hsrcLen : (S.R src).length = V := by simp [hsrc,replicaKeyWords,V]
  let M := payloadCountedState S count V
  have hframe (i : Fin T) (hi : i ≠ count) : M.R i = S.R i := Function.update_of_ne hi _ _
  have hcontrolFrame (i : Fin T) (hi : i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work]) :
      M.R i = S.R i := hframe i (hcountControls i hi)
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) := hframe _ (hcountOff j)
  have hvolume : (∑ j, (M.R (ι j)).length) = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbank]
  refine withPayloadCounter_exec_within src count saved (by regs_nodup) V _
    (packedGeneratedChunkTile hd re im hi hQre hQim ι hι hT
      src tmp saved count reRev imRev base one width powTmp powSaved a half par bits cnt work ps bs rs)
    (packedGeneratedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs)
    (packedChunkStockAllowance T d W c ps bs rs) depth
    v S hsrcLen hcount (hcodecBlank saved (by simp)) ?_
  intro u
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedGeneratedChunkTile_exec_within body hA hd re im hi hne hreHead himHead hQre hQim ι hι hT
    src tmp saved count reRev imRev hreg base one width exponent powTmp powSaved a half par bits cnt work
    ps bs hp hb hsep hbankOff hprotected prefixes suffixes hprefixes hsuffixes d W hW hgen hdisjoint hmaster hcontrols
    realBits imagBits u M
    (by rw [hcontrolFrame base (by simp)]; exact hbase)
    (by rw [hcontrolFrame one (by simp)]; exact hone)
    (by rw [hcontrolFrame width (by simp)]; exact hwidth)
    (by rw [hcontrolFrame exponent (by simp)]; exact hexponent)
    (by intro i hi; rw [hframe i (by intro he; exact hcountBank (he ▸ hi))]; exact hblank i hi)
    (by rw [hcontrolFrame powTmp (by simp)]; exact htmp)
    (by rw [hcontrolFrame powSaved (by simp)]; exact hsaved)
    hL
    (by intro j hj; rw [hbank]; exact hpriv j hj)
    (by intro k; rw [hbank]; exact hhdr k)
    (by
      intro i hi
      rw [hcontrolFrame i (List.mem_append_right [base,one,width,exponent,powTmp,powSaved] hi)]
      exact hgenBlank i hi)
    (by rw [hframe src ‹src ≠ count›]; exact hsrc)
    (by simp [M,payloadCountedState,V])
    (by
      intro i hi
      have hic : i ≠ count := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hframe i hic]
      exact hcodecBlank i hi)
    (by intro i hire hiim hheads s hs; rw [hbank] at hs; exact hother i hire hiim hheads s hs) depth
  rw [hvolume] at hn₂
  exact ⟨v₂,n₂,hu₂,hn₂,he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
