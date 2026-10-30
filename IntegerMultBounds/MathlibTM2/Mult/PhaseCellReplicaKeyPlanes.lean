module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyInterchange

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem replicaBits_good {K N D W : ℕ} (bits : Fin N → Fin D → Fin W → Bool)
    (s : Fin (prime+K+4)) (hs : s ∈ replicaKeyWords (fun r k b => bitSymbol (bits r k b))) :
    s ≠ blank ∧ s.val < prime+4 := by
  rw [←replicaKeyWords_map (bitSymbol (a := prime+K)) bits] at hs
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  exact bitSymbol_good b

private theorem keyBits_good {K N D W : ℕ} (bits : Fin N → Fin D → Fin W → Bool)
    (s : Fin (prime+K+4)) (hs : s ∈ keyReplicaWords (fun r k b => bitSymbol (bits r k b))) :
    s ≠ blank ∧ s.val < prime+4 := by
  rw [←keyReplicaWords_map (bitSymbol (a := prime+K)) bits] at hs
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  exact bitSymbol_good b

noncomputable def replicaKeyPlanesInterchange {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T) : Pr P T Q (prime+K) U :=
  .seq (placedSwapProg hd re hi hQre ι hι hT) (placedSwapProg hd im hi hQim ι hι hT)

/-- Both bit planes share one header/private bank. The second machine's
readiness follows from the first machine's exact frame and bit-format result. -/
theorem replicaKeyPlanesInterchange_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd) (hne : re ≠ im)
    (hreHead : ∀ k, hd k ≠ re)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (W h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ k, Counter.value (hs k) = swapValues 1 1 W h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hW : 0 < W)
    (realBits imagBits : Fin (2^h) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator::(hs k).map bitSymbol)
    (hre : S.R (ι (reg re)) = replicaKeyWords (fun r k b => bitSymbol (realBits r k b)))
    (him : S.R (ι (reg im)) = replicaKeyWords (fun r k b => bitSymbol (imagBits r k b)))
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 2*((T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
        6*∑ j, (S.R (ι j)).length+2*T+6*swapT t₀+15) ∧
      Exec body (replicaKeyPlanesInterchange hd re im hi hQre hQim ι hι hT) (mk v S) m
        (mk v' {S with L := fun _ => [], R := (Function.update (Function.update S.R (ι (reg re))
          (keyReplicaWords (fun r k b => bitSymbol (realBits r k b)))) (ι (reg im))
          (keyReplicaWords (fun r k b => bitSymbol (imagBits r k b))))}) := by
  have hplaced : Function.Injective (fun i : Fin t₀ => ι (reg i)) := hι.comp swapReg_injective
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := replicaKeyBitInterchange_exec body hd re hi hQre ι hι hT
    W h d hs hhd hdh hv hc hW realBits v S hL hpriv hhdr hre (by
      intro i hire hheads s hmem
      by_cases hiim : i = im
      · subst i; rw [him] at hmem; exact replicaBits_good imagBits s hmem
      · exact hother i hire hiim hheads s hmem)
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update S.R (ι (reg re))
    (keyReplicaWords (fun r k b => bitSymbol (realBits r k b))))}
  have hprivM : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → M.R (ι j) = [] := by
    intro j hj
    have hne : ι j ≠ ι (reg re) := by
      intro he
      have hh := congrArg Fin.val (hι he)
      have hr := re.isLt
      change j.val = re.val at hh
      omega
    simpa only [M,Function.update_of_ne hne] using hpriv j hj
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicaKeyBitInterchange_exec body hd im hi hQim ι hι hT
    W h d hs hhd hdh hv hc hW imagBits v₁ M (by intro i; rfl) hprivM
    (by intro k; simpa only [M,Function.update_of_ne (hplaced.ne (hreHead k))] using hhdr k)
    (by simpa only [M,Function.update_of_ne (hplaced.ne hne.symm)] using him)
    (by
      intro i hiim hheads s hmem
      by_cases hire : i = re
      · subst i
        simp only [M,Function.update_self] at hmem
        exact keyBits_good realBits s hmem
      · simp only [M,Function.update_of_ne (hplaced.ne hire)] at hmem
        exact hother i hire hiim hheads s hmem)
  have hlength : (keyReplicaWords (fun r k b => (bitSymbol (realBits r k b) : Fin (prime+K+4)))).length =
      (S.R (ι (reg re))).length := by
    rw [hre]
    simp [keyReplicaWords,replicaKeyWords,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have hvolume : ∑ j, (M.R (ι j)).length = ∑ j, (S.R (ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : ι j = ι (reg re)
    · simp only [M,he,Function.update_self]
      exact hlength
    · simp only [M,Function.update_of_ne he]
  rw [hvolume] at hn₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,?_⟩
  exact Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
