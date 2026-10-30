module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRouterCodec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBankVolume

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def packedReplicaKeyRouter {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T) : Pr P T Q (prime+K) U :=
  packedRouterUsing src (ι (reg re)) (ι (reg im)) tmp saved count reRev imRev
    (replicaKeyPlanesInterchange hd re im hi hQre hQim ι hι hT)

/-- Encode, group both bit planes, erase the old packed copy and reassemble.
Only the packed payload and its disposable symbol counter change. -/
theorem packedReplicaKeyRouter_exec {t₀ T Q K : ℕ} {U P : Type}
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
    (hcount : (S.R count).length = 2^h*(2^d*W))
    (hblank : ∀ i ∈ [ι (reg re),ι (reg im),tmp,saved,reRev,imRev], S.R i = [])
    (hother : ∀ i, i ≠ re → i ≠ im → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    let V := 2^h*(2^d*W)
    ∃ v' m, v'.user = v.user ∧
      m ≤ (12*V+12)+2*((T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
        6*((∑ j, (S.R (ι j)).length)+2*V)+2*T+6*swapT t₀+15)+(2*V+2)+(8*V+6) ∧
      Exec body (packedReplicaKeyRouter hd re im hi hQre hQim ι hι hT src tmp saved count reRev imRev) (mk v S) m
        (mk v' {S with L := fun _ => [], R := (Function.update (Function.update S.R src
          (keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)))) count [])}) := by
  dsimp only
  let V := 2^h*(2^d*W)
  have hr := hreg
  regs_ne hr
  have hplaced : Function.Injective (fun i : Fin t₀ => ι (reg i)) := hι.comp swapReg_injective
  let R := replicaKeyWords (fun r k b => (bitSymbol (realBits r k b) : Fin (prime+K+4)))
  let I := replicaKeyWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (prime+K+4)))
  let M := packedRouterPlaneInput S (ι (reg re)) (ι (reg im)) realBits imagBits
  have hprivM : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → M.R (ι j) = [] := by
    intro j hj
    have hoff (i : Fin t₀) : ι j ≠ ι (reg i) := by
      intro he
      have hh := congrArg Fin.val (hι he)
      have hi := i.isLt
      change j.val = i.val at hh
      omega
    simpa only [M,packedRouterPlaneInput,Function.update_of_ne (hoff re),Function.update_of_ne (hoff im)] using hpriv j hj
  have hvolume : ∑ j, (M.R (ι j)).length ≤ (∑ j, (S.R (ι j)).length)+2*V := by
    have h₁ := bank_volume_update_le ι hι S.R (reg re) R
    have h₂ := bank_volume_update_le ι hι (Function.update S.R (ι (reg re)) R) (reg im) I
    have hR : R.length = V := by simp [R,replicaKeyWords,V]
    have hI : I.length = V := by simp [I,replicaKeyWords,V]
    change (∑ j, (M.R (ι j)).length) ≤ _ at h₂
    omega
  refine packedRouterUsing_exec src (ι (reg re)) (ι (reg im)) tmp saved count reRev imRev hreg hA
    realBits imagBits (replicaKeyPlanesInterchange hd re im hi hQre hQim ι hι hT)
    (2*((T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
      6*((∑ j, (S.R (ι j)).length)+2*V)+2*T+6*swapT t₀+15)) v S hsrc hcount hblank ?_
  intro u
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicaKeyPlanesInterchange_exec body hd re im hi hne hreHead hQre hQim ι hι hT
    W h d hs hhd hdh hv hc hW realBits imagBits u M hL hprivM
    (by intro k; simpa only [M,packedRouterPlaneInput,Function.update_of_ne (hplaced.ne (hreHead k)),Function.update_of_ne (hplaced.ne (himHead k))] using hhdr k)
    (by simp only [M,packedRouterPlaneInput,R,Function.update_of_ne (hplaced.ne hne),Function.update_self])
    (by simp only [M,packedRouterPlaneInput,I,Function.update_self])
    (by intro i hire hiim hheads s hmem
        simp only [M,packedRouterPlaneInput,Function.update_of_ne (hplaced.ne hire),Function.update_of_ne (hplaced.ne hiim)] at hmem
        exact hother i hire hiim hheads s hmem)
  have hbill := Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hvolume)
      ((T+12*swapT t₀+5)*swapCost 1 1 W h d hs)) (2*T)) (6*swapT t₀)) 15)
  exact ⟨v₂,n₂,hu₂,hn₂.trans hbill,he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
