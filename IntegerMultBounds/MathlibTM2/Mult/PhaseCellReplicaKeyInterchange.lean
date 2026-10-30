module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout
public import IntegerMultBounds.MathlibTM2.Host.PlacedSwap

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Reuse the existing tape interchange to group all replicas by key at once.
The bit-encoding relation is explicit; encoding packed coefficient symbols,
padding nondyadic dimensions and generating headers remain caller obligations. -/
theorem replicaKeyInterchange_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (W h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ k, Counter.value (hs k) = swapValues 1 1 W h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hW : 0 < W)
    (x : Fin (BinaryAdjacentWidthInterchange.volume 1 (2^h) 1 (2^d) W) → Bool)
    (f : Fin (2^h) → Fin (2^d) → Fin W → Fin (prime+K+4))
    (hbits : (List.ofFn fun i => bitSymbol (x i)) = replicaKeyWords f)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator::(hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = replicaKeyWords f)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
        6*∑ j, (S.R (ι j)).length+2*T+6*swapT t₀+15 ∧
      Exec body (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) (keyReplicaWords f)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := placedSwapProg_exec body hd pay hi hQ ι hι hT
    1 1 W h d hs hhd hdh hv hc (by decide) (by decide) hW x v S hL hpriv hhdr
    (hpay.trans hbits.symm) hother
  exact ⟨v',m,hu,hm,by simpa only [hpay,replicaKeyWords_swap] using he⟩

/-- A genuine bit plane needs no externally supplied array/encoding witness. -/
theorem replicaKeyBitInterchange_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (W h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ k, Counter.value (hs k) = swapValues 1 1 W h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hW : 0 < W)
    (bits : Fin (2^h) → Fin (2^d) → Fin W → Bool)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator::(hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = replicaKeyWords (fun r k b => bitSymbol (bits r k b)))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
        6*∑ j, (S.R (ι j)).length+2*T+6*swapT t₀+15 ∧
      Exec body (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) (keyReplicaWords (fun r k b => bitSymbol (bits r k b)))}) := by
  obtain ⟨x,hx⟩ := replicaKeyWords_array bits
    (BinaryAdjacentWidthInterchange.volume 1 (2^h) 1 (2^d) W)
    (by simp [BinaryAdjacentWidthInterchange.volume,Nat.mul_assoc])
  have hbits := congrArg (List.map (bitSymbol (a := prime+K))) hx
  simp only [List.map_ofFn,replicaKeyWords_map,Function.comp_def] at hbits
  exact replicaKeyInterchange_exec body hd pay hi hQ ι hι hT W h d hs hhd hdh hv hc hW x
    (fun r k b => bitSymbol (bits r k b)) hbits v S hL hpriv hhdr hpay hother

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
