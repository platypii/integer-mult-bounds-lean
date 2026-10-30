module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaKeyRouter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyRoutingBill
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPayload

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def countedPackedReplicaKeyRouter {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T) : Pr P T Q (prime+K) U :=
  withPayloadCounter src count saved (packedReplicaKeyRouter hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev)

/-- Count the actual payload, route it, and restore the disposable counter.
The counter is outside the placed bank, so it adds no normalization volume. -/
theorem countedPackedReplicaKeyRouter_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd) (hne : re ≠ im)
    (hreHead : ∀ k, hd k ≠ re) (himHead : ∀ k, hd k ≠ im)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T)
    (hreg : [src,ι (reg re),ι (reg im),tmp,saved,count,reRev,imRev].Nodup)
    (W h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ k, Counter.value (hs k) = swapValues 1 1 W h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hW : 0 < W)
    (realBits imagBits : Fin (2^h) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator::(hs k).map bitSymbol)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))
    (hcount : S.R count = [])
    (hcountOff : ∀ j, ι j ≠ count)
    (hblank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ packedReplicaKeyRoutingCost T t₀ W h d (∑ j, (S.R (ι j)).length) hs ∧
      Exec body (countedPackedReplicaKeyRouter hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev) (mk v S) m
        (mk v' {S with L := fun _ => [], R := (Function.update S.R src
          (keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b))))}) := by
  dsimp only [packedReplicaKeyRoutingCost]
  let V := 2^h*(2^d*W)
  have hr := hreg
  regs_ne hr
  have hsrcLen : (S.R src).length = V := by simp [hsrc,replicaKeyWords,V]
  let M := payloadCountedState S count V
  have hbank (j : Fin (swapT t₀)) : M.R (ι j) = S.R (ι j) := Function.update_of_ne (hcountOff j) _ _
  have hvolume : ∑ j, (M.R (ι j)).length = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbank]
  refine withPayloadCounter_exec src count saved (by regs_nodup) V _
    (packedReplicaKeyRouter hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev) _
    v S hsrcLen hcount (hblank saved (by simp)) ?_
  intro u
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedReplicaKeyRouter_exec body hA hd re im hi hne hreHead himHead hQre hQim ι hι hT
    src tmp saved count reRev imRev hreg W h d hs hhd hdh hv hc hW realBits imagBits u M hL
    (by intro j hj; rw [hbank]; exact hpriv j hj)
    (by intro k; rw [hbank]; exact hhdr k)
    (by simpa only [M,payloadCountedState,Function.update_of_ne ‹src ≠ count›] using hsrc)
    (by simp [M,payloadCountedState,V])
    (by
      intro i hi
      have hic : i ≠ count := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      simpa only [M,payloadCountedState,Function.update_of_ne hic] using hblank i hi)
    (by intro i hire hiim hheads x hx; rw [hbank] at hx; exact hother i hire hiim hheads x hx)
  rw [hvolume] at hn₂
  exact ⟨v₂,n₂,hu₂,hn₂,he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
