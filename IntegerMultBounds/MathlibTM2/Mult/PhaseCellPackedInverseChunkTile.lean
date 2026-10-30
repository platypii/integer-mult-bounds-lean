module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratedChunkTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseChunkPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRouterCodec

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem packedGeneratedChunkTile_inverse_exec {t₀ T Q K c : ℕ} {U P : Type}
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
    (hsrc : S.R src = keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))
    (hcount : (S.R count).length = (2^d)^c*(2^d*W))
    (hcodecBlank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedGeneratedChunkTileCost T t₀ d W c (∑ j, (S.R (ι j)).length) ps bs rs ∧
      Exec body (packedGeneratedChunkTile hd re im hi hQre hQim ι hι hT
        src tmp saved count reRev imRev base one width powTmp powSaved
        a half par bits cnt work ps bs rs.reverse) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update (Function.update S.R src
          (replicaKeyWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))) count [])}) := by
  dsimp only [packedGeneratedChunkTileCost]
  let rs := wiredChunkStages (2^d) W one exponent prefixes suffixes
  let V := (2^d)^c*(2^d*W)
  have hr := hreg
  regs_ne hr
  have hplaced : Function.Injective (fun i : Fin t₀ => ι (reg i)) := hι.comp swapReg_injective
  let R := keyReplicaWords (fun r k b => (bitSymbol (realBits r k b) : Fin (prime+K+4)))
  let I := keyReplicaWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (prime+K+4)))
  let M := packedRouterPlaneInput S (ι (reg re)) (ι (reg im))
    (fun k r b => realBits r k b) (fun k r b => imagBits r k b)
  have hframe (i : Fin T) (hire : i ≠ ι (reg re)) (hiim : i ≠ ι (reg im)) : M.R i = S.R i := by
    simp only [M,packedRouterPlaneInput,Function.update_of_ne hire,Function.update_of_ne hiim]
  have hcontrolFrame (i : Fin T) (hi : i ∈ [base,one,width,exponent,powTmp,powSaved,a,half,par,bits,cnt,work]) :
      M.R i = S.R i := hframe i (hcontrols i hi).1 (hcontrols i hi).2
  have hvolume : (∑ j, (M.R (ι j)).length) ≤ (∑ j, (S.R (ι j)).length)+2*V := by
    have h₁ := bank_volume_update_le ι hι S.R (reg re) R
    have h₂ := bank_volume_update_le ι hι (Function.update S.R (ι (reg re)) R) (reg im) I
    have hR : R.length = V := by simp [R,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    have hI : I.length = V := by simp [I,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    change (∑ j, (M.R (ι j)).length) ≤ _ at h₂
    omega
  have hV : 2^d*((2^d)^c*W) = V := by dsimp [V]; ring
  have hroute : ∀ u : HS T Q (prime+K) U, ∃ u' n, u'.user = u.user ∧
      n ≤ 2*generatedChunkTileCost T t₀ d W ((∑ j, (S.R (ι j)).length)+2*V) ps bs rs ∧
      Exec body (generatedChunkPlanes hd re im hi hQre hQim ι hι hT base one width powTmp powSaved
        a half par bits cnt work ps bs rs.reverse) (mk u M) n
        (mk u' (packedRouterPlaneOutput S (ι (reg re)) (ι (reg im))
          (fun k r b => realBits r k b) (fun k r b => imagBits r k b))) := by
    intro u
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedChunkPlanes_inverse_exec body hd re im hi hne hreHead himHead hQre hQim ι hι hT
      base one width exponent powTmp powSaved a half par bits cnt work ps bs hp hb hsep hbankOff hprotected
      prefixes suffixes hprefixes hsuffixes d W hW hgen hdisjoint hmaster hcontrols realBits imagBits u M
      (by rw [hcontrolFrame base (by simp)]; exact hbase)
      (by rw [hcontrolFrame one (by simp)]; exact hone)
      (by rw [hcontrolFrame width (by simp)]; exact hwidth)
      (by rw [hcontrolFrame exponent (by simp)]; exact hexponent)
      (by intro i hi; rw [hframe i (hbankOff i hi (reg re)) (hbankOff i hi (reg im))]; exact hblank i hi)
      (by rw [hcontrolFrame powTmp (by simp)]; exact htmp)
      (by rw [hcontrolFrame powSaved (by simp)]; exact hsaved)
      hL
      (by
        intro j hj
        have hoff (i : Fin t₀) : ι j ≠ ι (reg i) := by
          intro he
          have hh := congrArg Fin.val (hι he)
          change j.val = i.val at hh
          have hi := i.isLt
          omega
        rw [hframe _ (hoff re) (hoff im)]
        exact hpriv j hj)
      (by intro k; rw [hframe _ (hplaced.ne (hreHead k)) (hplaced.ne (himHead k))]; exact hhdr k)
      (by
        intro i hi
        rw [hcontrolFrame i (List.mem_append_right [base,one,width,exponent,powTmp,powSaved] hi)]
        exact hgenBlank i hi)
      (by simp only [M,packedRouterPlaneInput,Function.update_of_ne (hplaced.ne hne),Function.update_self,keyReplicaWords,replicaKeyWords_map])
      (by simp only [M,packedRouterPlaneInput,Function.update_self,keyReplicaWords,replicaKeyWords_map])
      (by intro i hire hiim hheads s hs; rw [hframe _ (hplaced.ne hire) (hplaced.ne hiim)] at hs; exact hother i hire hiim hheads s hs)
    refine ⟨v₂,n₂,hu₂,hn₂.trans (Nat.mul_le_mul_left 2 (generatedChunkTileCost_mono ps bs rs hvolume)),?_⟩
    simpa only [packedRouterPlaneOutput,keyReplicaWords,replicaKeyWords_map] using he₂

  have he := packedRouterUsing_exec (body := body) src (ι (reg re)) (ι (reg im)) tmp saved count reRev imRev hreg hA
    (fun k r b => realBits r k b) (fun k r b => imagBits r k b)
    (generatedChunkPlanes hd re im hi hQre hQim ι hι hT base one width powTmp powSaved
      a half par bits cnt work ps bs rs.reverse)
    (2*generatedChunkTileCost T t₀ d W ((∑ j, (S.R (ι j)).length)+2*V) ps bs rs)
    v S hsrc (by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hcount) hcodecBlank hroute
  simpa only [hV,keyReplicaWords,packedGeneratedChunkTile] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
