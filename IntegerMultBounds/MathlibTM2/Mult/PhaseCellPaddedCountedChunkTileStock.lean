module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedCountedChunkTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPackedGeneratedChunkTileStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedReplicaTileStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Pad a short owned replica tile and route it with generated counters,
headers and dimensions. The same scratch ports serve both phases. -/
theorem paddedCountedChunkTile_exec_within {t₀ T Q K c N : ℕ} {U P : Type}
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
    (realBits imagBits : Fin N → Fin (2^d) → Fin W → Bool)
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
    ∃ (r i : Fin ((2^d)^c) → Fin (2^d) → Fin W → Bool), ∃ v' n,
      v'.user = v.user ∧
      n ≤ paddedCountedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (74*((2^d)^c*(2^d*W))+56)+(2*(4*((2^d)^c*(2^d*W))+4)+
          packedChunkStockAllowance T d W c ps bs rs)) depth (paddedCountedChunkTile c hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev
        base one width exponent powTmp powSaved a half par bits cnt work ps bs rs) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update S.R src
          (keyReplicaWords (fun a k b => pairSym (prime+K) (r a k b) (i a k b))))}) ∧
      (replicaKeyWords (fun a k b => pairSym (prime+K) (r a k b) (i a k b))).drop
        (((2^d)^c-N)*(2^d*W)) = S.R src := by
  dsimp only [paddedCountedChunkTileCost]
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  have hr := hreg
  regs_ne hr
  obtain ⟨r,i,v₁,n₁,hu₁,hn₁,he₁,hreal⟩ := generatedReplicaTilePadding_exec_within (body := body) c exponent width src a count tmp saved
    hpadReg d W hW hN realBits imagBits v S hexponent hwidth hsrc (hgenBlank a (by simp)) hcount
    (hcodecBlank tmp (by simp)) (hcodecBlank saved (by simp)) depth
  let M : Stacks T (prime+K) := {S with R := (Function.update S.R src
    (replicaKeyWords (fun a k b => pairSym (prime+K) (r a k b) (i a k b))))}
  have hframe (j : Fin T) (hj : j ≠ src) : M.R j = S.R j := Function.update_of_ne hj _ _
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) := hframe _ (hsourceOff j)
  have hcontrolFrame (j : Fin T) (hj : j ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work]) :
      M.R j = S.R j := hframe j (hsourceControls j hj)
  have hvolume : (∑ j, (M.R (ι j)).length) = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbank]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := countedPackedGeneratedChunkTile_exec_within body hA hd re im hi hne hreHead himHead hQre hQim ι hι hT
    src tmp saved count reRev imRev hreg base one width exponent powTmp powSaved a half par bits cnt work
    ps bs hp hb hsep hbankOff hprotected prefixes suffixes hprefixes hsuffixes d W hW hgen hdisjoint hmaster hcontrols
    r i v₁ M
    (by rw [hcontrolFrame base (by simp)]; exact hbase)
    (by rw [hcontrolFrame one (by simp)]; exact hone)
    (by rw [hcontrolFrame width (by simp)]; exact hwidth)
    (by rw [hcontrolFrame exponent (by simp)]; exact hexponent)
    (by intro j hj; rw [hframe j (by intro he; exact hsourceBank (he ▸ hj))]; exact hblank j hj)
    (by rw [hcontrolFrame powTmp (by simp)]; exact htmp)
    (by rw [hcontrolFrame powSaved (by simp)]; exact hsaved)
    hL
    (by intro j hj; rw [hbank]; exact hpriv j hj)
    (by intro k; rw [hbank]; exact hhdr k)
    (by intro j hj; rw [hcontrolFrame j (List.mem_append_right [base,one,width,exponent,powTmp,powSaved] hj)]; exact hgenBlank j hj)
    (by simp [M])
    (by rw [hframe count ‹src ≠ count›.symm]; exact hcount)
    (by
      intro j hj
      have hjs : j ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hframe j hjs]
      exact hcodecBlank j hj)
    hcountOff hcountControls hcountBank
    (by intro j hjr hji hheads s hs; rw [hbank] at hs; exact hother j hjr hji hheads s hs) depth
  rw [hvolume] at hn₂
  refine ⟨r,i,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,hreal⟩
  let extra := 2*(4*((2^d)^c*(2^d*W))+4)+packedChunkStockAllowance T d W c ps bs rs
  let bound := mnSize (mk v S)+depth+(74*((2^d)^c*(2^d*W))+56)+extra
  have hs := he₁.final
  change mnSize (mk v₁ M)+depth ≤ mnSize (mk v S)+depth+(74*((2^d)^c*(2^d*W))+56) at hs
  have hw₁ := he₁.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    have hc' : mnSize state+z ≤ mnSize (mk v S)+depth+(74*((2^d)^c*(2^d*W))+56) := by
      simpa only [Nat.add_assoc] using hc
    exact hc'.trans (Nat.le_add_right _ extra))
  have hw₂ := he₂.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    have hc' : mnSize state+z ≤ mnSize (mk v₁ M)+depth+extra := by
      simpa only [extra,Nat.add_assoc] using hc
    exact hc'.trans (Nat.add_le_add_right hs extra))
  have he := ExecWithin.seq hw₁ hw₂
  have hout : mk v₂ {M with L := fun _ => [], R := (Function.update M.R src
      (keyReplicaWords (fun a k b => pairSym (prime+K) (r a k b) (i a k b))))} =
      mk v₂ {S with L := fun _ => [], R := (Function.update S.R src
      (keyReplicaWords (fun a k b => pairSym (prime+K) (r a k b) (i a k b))))} := by
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j = src
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj,M]
  exact (congrArg (fun f => ExecWithin body (fun z state => mnSize state+z ≤ bound) depth
    (paddedCountedChunkTile c hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev
      base one width exponent powTmp powSaved a half par bits cnt work ps bs rs)
    (mk v S) (n₁+n₂) f) hout).mp he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
