module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationTileBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveRowsChunkTile
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

theorem archiveTilePublication_exec {t₀ T Q K c N s : ℕ} {U P : Type}
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
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4)
    (clock padRows wordWidth retireCount control savedControl gap window dst acc trash pubTmp lineRows outAcc pubSaved : Fin T)
    (hpubReg : [clock,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,pubTmp,lineRows,outAcc,pubSaved].Nodup)
    (windows : PublicationWindows s L) (hwindowCount : N = windows.origins.length) (hw1 : 1 ≤ w)
    (ambient : Fin (2^d) → List (Fin (prime+K+4))) (outputTail : List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*w)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = 2^d)
    (hpadRows : (S.R padRows).length = ((2^d)^c-N)*L)
    (hwordWidth : (S.R wordWidth).length = w) (hlineRows : (S.R lineRows).length = s)
    (hcontrol : S.R control = gatherControls (prime+K) (windows.gaps w))
    (hwindow : (S.R window).length = L*w)
    (hpubClean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,pubTmp,pubSaved,outAcc], S.R i = []) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' F n, v'.user = v.user ∧
      n ≤ paddedCountedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs+
        ((2^d)*(replicaPublicationStepCost s ((2^d)^c-N) L w+3)+2+(2*((2^d)*(s*w))+2)) ∧
      Exec body (.seq (paddedCountedChunkTile c hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev
          base one width exponent powTmp powSaved a half par bits cnt work ps bs rs) (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash pubTmp lineRows outAcc pubSaved))
          (moveR outAcc dst id))) (mk v S) n (mk v' F) ∧
      F.R src = [] ∧
      F.R dst = (List.ofFn fun j => scatterRows (L*w) (ambient j)
        (cstream (prime+K) w (List.ofFn fun i => tileRows i j).flatten) (windows.gaps w)).flatten++outputTail ∧
      F.R outAcc = [] ∧ F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  obtain ⟨paddedRows,hpadded,hreal,v₁,n₁,hu₁,hn₁,he₁⟩ := paddedArchiveRowsChunkTile_exec body hA
    hd re im hi hne hreHead himHead hQre hQim ι hι hT src tmp saved count reRev imRev hreg
    base one width exponent powTmp powSaved a half par bits cnt work hpadReg hsourceOff hsourceControls
    ps bs hp hb hsep hbankOff hsourceBank hprotected prefixes suffixes hprefixes hsuffixes d W hW hN
    hgen hdisjoint hmaster hcontrols L w hpacket tileRows htileRows v S hbase hone hwidth hexponent
    hblank htmp hsaved hL hpriv hhdr hgenBlank hsrc hcount hcodecBlank hcountOff hcountControls hcountBank hother
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hdst',ha,hclock',hi',ho',hl',hframe⟩ := publicationTileBank_exec body
    src clock padRows wordWidth retireCount control savedControl gap window dst acc trash pubTmp lineRows outAcc pubSaved
    hpubReg windows w hN hwindowCount hw1 tileRows paddedRows htileRows hpadded hreal ambient outputTail hambient v₁ S
    hdst hclock hpadRows hwordWidth hlineRows hcontrol hwindow hpubClean
  have hleft : (fun _ : Fin T => ([] : List (Fin (prime+K+4)))) = S.L := by
    funext i; exact (hL i).symm
  rw [hleft] at he₁
  exact ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    hs,hdst',ha,hclock',hi',ho',hl',hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
