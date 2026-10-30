module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBankVolume
public import IntegerMultBounds.MathlibTM2.Host.PlacedSwap
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def generatedChunkInterchange {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (a half par bits cnt work : Fin T) : Pr P T Q (prime+K) U :=
  .seq (replicaKeyHeaders dims (fun k => ι (reg (hd k))) a half par bits cnt work)
    (.seq (placedSwapProg hd pay hi hQ ι hι hT)
      (clearWords (List.ofFn fun k => ι (reg (hd k)))))

/-- One actual equal-width chunk stage with generated and erased headers.
The prefix multiplicity and trailing block width can vary between stages. -/
theorem generatedChunkInterchange_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (a half par bits cnt work : Fin T)
    (hgen : ∀ k, [dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ k j, ι (reg (hd k)) ≠ dims j)
    (outerCount blockWidth d : ℕ) (houter : 0 < outerCount) (hblock : 0 < blockWidth)
    (x : Fin (BinaryAdjacentWidthInterchange.volume outerCount (2^d) 1 (2^d) blockWidth) → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ k, (S.R (dims k)).length = swapValues outerCount 1 blockWidth d d k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = List.ofFn (fun i => bitSymbol (x i)))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let H := interchangeHeaderVolume outerCount 1 blockWidth d d
    let hs := interchangeHeaderBits outerCount 1 blockWidth d d
    ∃ v' n, v'.user = v.user ∧
      n ≤ (21*(outerCount+1+blockWidth+d+d)+56)+
        ((T+12*swapT t₀+5)*swapCost outerCount 1 blockWidth d d hs+
          6*((∑ j, (S.R (ι j)).length)+H)+2*T+6*swapT t₀+15)+(2*H+11) ∧
      Exec body (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          (swapList outerCount (2^d) 1 (2^d) blockWidth blank (S.R (ι (reg pay)))))}) := by
  dsimp only
  let dst := fun k => ι (reg (hd k))
  have hdst : Function.Injective dst := fun i j he => hi (BinaryInterchangeRun.slot_injective (hι he))
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hheaders,hoff,hv,hc⟩ := interchangeHeaders_exec
    dims dst hdst a half par bits cnt work hgen hdisjoint outerCount 1 blockWidth d d v S hdims hhdr hgenBlank
  let R := canonicalHeaderListR (fun i => (S.R i).length) (replicaKeyHeaderFields dims dst) S.R
  let M : Stacks T (prime+K) := {S with R := R}
  have hframe (i : Fin T) (hi : ∀ k, dst k ≠ i) : M.R i = S.R i := hoff i hi
  have hsrcOff (k : Fin 5) : dst k ≠ ι (reg pay) := by
    intro he
    exact hpay k (BinaryInterchangeRun.slot_injective (hι he))
  have hsource : M.R (ι (reg pay)) = S.R (ι (reg pay)) := hframe _ hsrcOff
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedSwapProg_exec body hd pay hi hQ ι hι hT
    outerCount 1 blockWidth d d (interchangeHeaderBits outerCount 1 blockWidth d d)
    (by omega) (by omega) hv hc houter (by decide) hblock x v₁ M hL
    (by
      intro j hj
      rw [hframe]
      · exact hpriv j hj
      · intro k he
        have hh := congrArg Fin.val (hι he)
        change (hd k).val = j.val at hh
        have hk := (hd k).isLt
        omega)
    hheaders (hsource.trans hsrc)
    (by
      intro i hip hheads s hs
      rw [hframe] at hs
      · exact hother i hip hheads s hs
      · intro k he
        exact hheads k (BinaryInterchangeRun.slot_injective (hι he)))
  have hstock : (∑ j, (M.R (ι j)).length) =
      (∑ j, (S.R (ι j)).length)+interchangeHeaderVolume outerCount 1 blockWidth d d := by
    have hh := bank_volume_of_frame (fun k => reg (hd k))
      (fun i j he => hi (BinaryInterchangeRun.slot_injective he))
      (fun j => S.R (ι j)) (fun j => M.R (ι j))
      (fun k => separator::(interchangeHeaderBits outerCount 1 blockWidth d d k).map (bitSymbol (a := prime+K)))
      hhdr hheaders (by intro j hj; apply hframe; intro k he; exact hj k (hι he))
    simpa only [List.length_cons,List.length_map,interchangeHeaderVolume,List.sum_ofFn] using hh
  rw [hstock] at hn₂
  let payload := swapList outerCount (2^d) 1 (2^d) blockWidth blank (S.R (ι (reg pay)))
  let F : Stacks T (prime+K) := {M with L := fun _ => [], R := Function.update M.R (ι (reg pay)) payload}
  have he₂' : Exec body (placedSwapProg hd pay hi hQ ι hι hT) (mk v₁ M) n₂ (mk v₂ F) := by
    simpa only [hsource] using he₂
  have hfinalHeader (k : Fin 5) : F.R (dst k) = separator::(interchangeHeaderBits outerCount 1 blockWidth d d k).map bitSymbol := by
    rw [show F.R (dst k) = M.R (dst k) from Function.update_of_ne (hsrcOff k) _ _]
    exact hheaders k
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn dst) (List.nodup_ofFn_ofInjective hdst) v₂ F
  have hcost : ((List.ofFn dst).map (fun i => (F.R i).length)).sum = interchangeHeaderVolume outerCount 1 blockWidth d d := by
    simp only [List.map_ofFn,Function.comp_def,hfinalHeader,List.length_cons,List.length_map,interchangeHeaderVolume]
  have hlength : (List.ofFn dst).length = 5 := List.length_ofFn
  refine ⟨v₃,n₁+n₂+(2*((List.ofFn dst).map (fun i => (F.R i).length)).sum+2*(List.ofFn dst).length+1),
    hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · rw [hcost,hlength]
    exact Nat.add_le_add_right (Nat.add_le_add hn₁ hn₂) _
  · refine (Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by omega) ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hh : i ∈ List.ofFn dst
    · obtain ⟨k,hki⟩ := List.mem_ofFn.mp hh
      subst i
      simp only [hh,ite_true]
      rw [Function.update_of_ne (hsrcOff k)]
      exact (hhdr k).symm
    · have hi : ∀ k, dst k ≠ i := by intro k he; exact hh (List.mem_ofFn.mpr ⟨k,he⟩)
      simp only [hh,ite_false]
      by_cases his : i = ι (reg pay)
      · subst i; simp only [F,Function.update_self,payload]
      · rw [show F.R i = M.R i from Function.update_of_ne his _ _,hframe i hi]
        exact (Function.update_of_ne his _ _).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
