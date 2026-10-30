module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPackedReplicaKeyRouter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBankVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyRoutingCost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def generatedPackedReplicaKeyRouter {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (a half par bits cnt work : Fin T)
    (src tmp saved count reRev imRev : Fin T) : Pr P T Q (prime+K) U :=
  .seq (replicaKeyHeaders dims (fun k => ι (reg (hd k))) a half par bits cnt work)
    (.seq (countedPackedReplicaKeyRouter hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev)
      (clearWords (List.ofFn fun k => ι (reg (hd k)))))

/-- Generate the five binary headers, execute the actual counted packed router,
and erase the headers. Only the payload changes. -/
theorem generatedPackedReplicaKeyRouter_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd) (hne : re ≠ im)
    (hreHead : ∀ k, hd k ≠ re) (himHead : ∀ k, hd k ≠ im)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T)
    (hreg : [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev].Nodup)
    (dims : Fin 5 → Fin T) (a half par bits cnt work : Fin T)
    (hgen : ∀ k, [dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ k j, ι (reg (hd k)) ≠ dims j)
    (hheadOff : ∀ k, ∀ i ∈ [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev],
      ι (reg (hd k)) ≠ i)
    (W h d : ℕ) (hhd : h ≤ d+1) (hdh : d ≤ h+1) (hW : 0 < W)
    (realBits imagBits : Fin (2^h) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ k, (S.R (dims k)).length = swapValues 1 1 W h d k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))
    (hcount : S.R count = [])
    (hcountOff : ∀ j, ι j ≠ count)
    (hblank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ generatedPackedReplicaKeyRoutingCost T t₀ W h d (∑ j, (S.R (ι j)).length) ∧
      Exec body (generatedPackedReplicaKeyRouter hd re im hi hQre hQim ι hι hT dims a half par bits cnt work src tmp saved count reRev imRev)
        (mk v S) m (mk v' {S with L := fun _ => [], R := (Function.update S.R src
          (keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b))))}) := by
  dsimp only [generatedPackedReplicaKeyRoutingCost]
  let dst := fun k => ι (reg (hd k))
  have hdst : Function.Injective dst := fun i j he => hi (BinaryInterchangeRun.slot_injective (hι he))
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hheaders,hoff,hv,hc⟩ := replicaKeyHeaders_exec
    dims dst hdst a half par bits cnt work hgen hdisjoint W h d v S hdims hhdr hgenBlank
  let R := canonicalHeaderListR (fun i => (S.R i).length) (replicaKeyHeaderFields dims dst) S.R
  let M : Stacks T (prime+K) := {S with R := R}
  have hframe (i : Fin T) (hi : ∀ k, dst k ≠ i) : M.R i = S.R i := hoff i hi
  have hcodec (i : Fin T) (hi : i ∈ [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev]) :
      M.R i = S.R i := hframe i (fun k => hheadOff k i hi)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := countedPackedReplicaKeyRouter_exec body hA hd re im hi hne hreHead himHead
    hQre hQim ι hι hT src tmp saved count reRev imRev hreg W h d (replicaKeyHeaderBits W h d)
    hhd hdh hv hc hW realBits imagBits v₁ M hL
    (by
      intro j hj
      rw [hframe]
      · exact hpriv j hj
      · intro k he
        have hh := congrArg Fin.val (hι he)
        change (hd k).val = j.val at hh
        have hk := (hd k).isLt
        omega)
    hheaders
    (by rw [hcodec src (by simp)]; exact hsrc)
    (by rw [hcodec count (by simp)]; exact hcount) hcountOff
    (by
      intro i hi
      have hi' : i ∈ [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        rcases hi with h | h | h | h | h | h <;> simp [h]
      rw [hcodec i hi']
      exact hblank i hi)
    (by
      intro i hire hiim hheads x hx
      rw [hframe] at hx
      · exact hother i hire hiim hheads x hx
      · intro k he
        exact hheads k (BinaryInterchangeRun.slot_injective (hι he)))
  have hstock : (∑ j, (M.R (ι j)).length) =
      (∑ j, (S.R (ι j)).length)+replicaKeyHeaderVolume W h d := by
    have hh := bank_volume_of_frame (fun k => reg (hd k))
      (fun i j he => hi (BinaryInterchangeRun.slot_injective he))
      (fun j => S.R (ι j)) (fun j => M.R (ι j))
      (fun k => separator::(replicaKeyHeaderBits W h d k).map (bitSymbol (a := prime+K)))
      hhdr hheaders (by
        intro j hj
        apply hframe
        intro k he
        exact hj k (hι he))
    simpa only [List.length_cons,List.length_map,replicaKeyHeaderVolume,List.sum_ofFn] using hh
  rw [hstock] at hn₂
  let payload := keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b))
  let F : Stacks T (prime+K) := {M with L := fun _ => [], R := Function.update M.R src payload}
  have hsrcOff (k : Fin 5) : dst k ≠ src := hheadOff k src (by simp)
  have hfinalHeader (k : Fin 5) : F.R (dst k) = separator::(replicaKeyHeaderBits W h d k).map bitSymbol := by
    rw [show F.R (dst k) = M.R (dst k) from Function.update_of_ne (hsrcOff k) _ _]
    exact hheaders k
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn dst) (List.nodup_ofFn_ofInjective hdst) v₂ F
  have hcost : ((List.ofFn dst).map (fun i => (F.R i).length)).sum = replicaKeyHeaderVolume W h d := by
    simp only [List.map_ofFn,Function.comp_def,hfinalHeader,List.length_cons,List.length_map,replicaKeyHeaderVolume]
  have hlength : (List.ofFn dst).length = 5 := List.length_ofFn
  refine ⟨v₃,n₁+n₂+(2*((List.ofFn dst).map (fun i => (F.R i).length)).sum+2*(List.ofFn dst).length+1),
    hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · rw [hcost,hlength]
    exact Nat.add_le_add_right (Nat.add_le_add hn₁ hn₂) _
  · refine (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hh : i ∈ List.ofFn dst
    · obtain ⟨k,hki⟩ := List.mem_ofFn.mp hh
      subst i
      simp only [hh,ite_true]
      rw [Function.update_of_ne (hsrcOff k)]
      exact (hhdr k).symm
    · have hi : ∀ k, dst k ≠ i := by
        intro k he
        exact hh (List.mem_ofFn.mpr ⟨k,he⟩)
      simp only [hh,ite_false]
      by_cases his : i = src
      · subst i; simp only [F,Function.update_self,payload]
      · rw [show F.R i = M.R i from Function.update_of_ne his _ _,hframe i hi]
        exact (Function.update_of_ne his _ _).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
