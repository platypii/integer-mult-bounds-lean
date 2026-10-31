module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedCoefficientChunkTile

/-! Execute short archive padding and coefficient transpose with derived rows.
Real core rows remain byte-for-byte unchanged at their shifted core indices. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem paddedArchiveRowsChunkTile_exec {t₀ T Q K c N : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hne : re ≠ im) (hreHead : ∀ k, hd k ≠ re) (himHead : ∀ k, hd k ≠ im)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T)
    (hreg : [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev].Nodup)
    (base one width exponent powTmp powSaved a half par bits cnt work : Fin T)
    (hpadReg : [exponent,width,src,a,count,tmp,saved].Nodup)
    (hsourceOff : ∀ j, ι j ≠ src)
    (hsourceControls : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work], i ≠ src)
    (ps bs : List (Fin T))
    (hp : ([base,powTmp,powSaved,one]++ps).Nodup) (hb : ([base,powTmp,powSaved,width]++bs).Nodup)
    (hsep : ∀ p ∈ one::ps, ∀ b ∈ width::bs, p ≠ b)
    (hbankOff : ∀ i ∈ ps++bs, ∀ j, i ≠ ι j)
    (hsourceBank : src ∉ ps++bs)
    (hprotected : ∀ i ∈ [a,half,par,bits,cnt,work,exponent], i ∉ ps++bs)
    (prefixes suffixes : Fin c → Fin T)
    (hprefixes : List.ofFn prefixes = one::ps) (hsuffixes : List.ofFn suffixes = width::bs)
    (d W : ℕ) (hW : 0 < W) (hN : N ≤ (2^d)^c)
    (hgen : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, r.dims k ≠ ι (reg re) ∧ r.dims k ≠ ι (reg im))
    (hcontrols : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work],
      i ≠ ι (reg re) ∧ i ≠ ι (reg im))
    (L w : ℕ) (hpacket : W = L*w)
    (tileRows : Fin N → Fin (2^d) → List GaussianInt)
    (htileRows : ∀ i j, (tileRows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hbase : (S.R base).length = 2^d) (hone : (S.R one).length = 1)
    (hwidth : (S.R width).length = W) (hexponent : (S.R exponent).length = d)
    (hblank : ∀ i ∈ ps++bs, S.R i = []) (htmp : S.R powTmp = []) (hsaved : S.R powSaved = [])
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R src = (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (tileRows i j)).flatten).flatten)
    (hcount : S.R count = [])
    (hcodecBlank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hcountOff : ∀ j, ι j ≠ count)
    (hcountControls : ∀ i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work], i ≠ count)
    (hcountBank : count ∉ ps++bs)
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ paddedRows : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt,
      (∀ i j, (paddedRows i j).length = L) ∧
      (∀ i j, paddedRows (paddedCoreIndex hN i) j = tileRows i j) ∧
      ∃ v' n,
      v'.user = v.user ∧
      n ≤ paddedCountedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (paddedCountedChunkTile c hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev
        base one width exponent powTmp powSaved a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update S.R src
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => paddedRows i j).flatten).flatten))}) := by
  let f := fun i j (k : Fin L) => (tileRows i j)[k.val]'(by rw [htileRows]; exact k.isLt)
  have hinput := archiveRows_cstream (A := prime+K) w tileRows htileRows
  obtain ⟨g,hpad,v',n,hu,hn,he,_⟩ := paddedCoefficientChunkTile_exec body hA hd re im hi hne
    hreHead himHead hQre hQim ι hι hT src tmp saved count reRev imRev hreg
    base one width exponent powTmp powSaved a half par bits cnt work hpadReg hsourceOff hsourceControls
    ps bs hp hb hsep hbankOff hsourceBank hprotected prefixes suffixes hprefixes hsuffixes d W hW hN
    hgen hdisjoint hmaster hcontrols L w hpacket f v S hbase hone hwidth hexponent hblank htmp hsaved
    hL hpriv hhdr hgenBlank (hsrc.trans hinput.symm) hcount hcodecBlank hcountOff hcountControls hcountBank hother
  let paddedRows := fun i j => List.ofFn (g i j)
  have hlength : ∀ i j, (paddedRows i j).length = L := by intro i j; simp [paddedRows]
  have hview : (fun i j (k : Fin L) => (paddedRows i j)[k.val]'(by rw [hlength]; exact k.isLt)) = g := by
    funext i j k
    simp only [paddedRows,List.getElem_ofFn]
  have houtput := routedArchiveRows_cstream (A := prime+K) w paddedRows hlength
  rw [hview] at houtput
  refine ⟨paddedRows,hlength,?_,v',n,hu,hn,?_⟩
  · intro i j
    apply List.ext_getElem (by simp [paddedRows,htileRows])
    intro k hk hk'
    simp only [paddedRows,List.getElem_ofFn]
    exact paddedCore_entry hN (0 : GaussianInt) f g hpad i j ⟨k,by simpa only [htileRows] using hk'⟩
  · simpa only [houtput] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
