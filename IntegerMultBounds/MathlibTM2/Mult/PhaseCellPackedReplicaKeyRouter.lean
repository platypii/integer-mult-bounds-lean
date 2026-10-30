module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlaneData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinBitPlanes

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem placed_update_volume {T B A : ℕ} (ι : Fin B → Fin T) (hι : Function.Injective ι)
    (R : Fin T → List (Fin (A+4))) (x : Fin B) (ys : List (Fin (A+4))) :
    (∑ j, (Function.update R (ι x) ys (ι j)).length) ≤ (∑ j, (R (ι j)).length)+ys.length := by
  calc
    _ ≤ ∑ j, ((R (ι j)).length+if j = x then ys.length else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases he : j = x
      · subst j; simp
      · simp only [Function.update_of_ne (hι.ne he),ite_eq_right he,Nat.add_zero,Nat.le_refl]
    _ = _ := by simp [Finset.sum_add_distrib]

noncomputable def packedReplicaKeyRouter {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (re im : Fin t₀) (hi : Function.Injective hd)
    (hQre : swapStates hd re hi ≤ Q) (hQim : swapStates hd im hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (src tmp saved count reRev imRev : Fin T) : Pr P T Q (prime+K) U :=
  .seq (copyPairBitPlanes src (ι (reg re)) (ι (reg im)) tmp saved)
    (.seq (replicaKeyPlanesInterchange hd re im hi hQre hQim ι hι hT)
      (.seq (uclear src) (joinBitPlanes count (ι (reg re)) (ι (reg im)) reRev imRev src)))

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
  have hsrcLen : (S.R src).length = V := by simp [hsrc,replicaKeyWords,V]
  obtain ⟨v₁,hu₁,he₁⟩ := copyPairBitPlanes_exec (body := body) src (ι (reg re)) (ι (reg im)) tmp saved
    (by regs_nodup) v S (hblank tmp (by simp)) (hblank saved (by simp))
  let R := replicaKeyWords (fun r k b => (bitSymbol (realBits r k b) : Fin (prime+K+4)))
  let I := replicaKeyWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (prime+K+4)))
  let M : Stacks T (prime+K) := {S with R := Function.update (Function.update S.R (ι (reg re)) R) (ι (reg im)) I}
  have he₁' : Exec body (copyPairBitPlanes src (ι (reg re)) (ι (reg im)) tmp saved) (mk v S) (12*V+12) (mk v₁ M) := by
    rw [hsrcLen] at he₁
    simpa only [M,R,I,hsrc,hblank (ι (reg re)) (by simp),hblank (ι (reg im)) (by simp),List.append_nil,
      replicaKeyPair_real hA,replicaKeyPair_imag hA] using he₁
  have hprivM : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → M.R (ι j) = [] := by
    intro j hj
    have hoff (i : Fin t₀) : ι j ≠ ι (reg i) := by
      intro he
      have hh := congrArg Fin.val (hι he)
      have hi := i.isLt
      change j.val = i.val at hh
      omega
    simpa only [M,Function.update_of_ne (hoff re),Function.update_of_ne (hoff im)] using hpriv j hj
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicaKeyPlanesInterchange_exec body hd re im hi hne hreHead hQre hQim ι hι hT
    W h d hs hhd hdh hv hc hW realBits imagBits v₁ M hL hprivM
    (by intro k; simpa only [M,Function.update_of_ne (hplaced.ne (hreHead k)),Function.update_of_ne (hplaced.ne (himHead k))] using hhdr k)
    (by simp only [M,R,Function.update_of_ne (hplaced.ne hne),Function.update_self])
    (by simp only [M,I,Function.update_self])
    (by intro i hire hiim hheads s hmem
        simp only [M,Function.update_of_ne (hplaced.ne hire),Function.update_of_ne (hplaced.ne hiim)] at hmem
        exact hother i hire hiim hheads s hmem)
  let RK := keyReplicaWords (fun r k b => (bitSymbol (realBits r k b) : Fin (prime+K+4)))
  let IK := keyReplicaWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (prime+K+4)))
  let N : Stacks T (prime+K) := {M with L := fun _ => [], R := Function.update (Function.update M.R (ι (reg re)) RK) (ι (reg im)) IK}
  have hNsrc : N.R src = S.R src := by
    simp only [N,M,Function.update_of_ne ‹src ≠ ι (reg im)›,Function.update_of_ne ‹src ≠ ι (reg re)›]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body src v₂ N
  rw [hNsrc,hsrcLen] at he₃
  let B : Stacks T (prime+K) := {N with R := Function.update N.R src []}
  let xs := keyReplicaWords realBits
  let ys := keyReplicaWords imagBits
  have hxs : xs.length = V := by simp [xs,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have hys : ys.length = V := by simp [ys,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := joinBitPlanes_exec (body := body) count (ι (reg re)) (ι (reg im)) reRev imRev src
    (by regs_nodup) hA xs ys (hxs.trans hys.symm) v₃ B
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,N,M,hxs,V] using hcount)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,N,M,xs,RK,keyReplicaWords_map])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,N,M,ys,IK,keyReplicaWords_map])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,N,M] using hblank reRev (by simp))
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,N,M] using hblank imRev (by simp))
  have hvolume : ∑ j, (M.R (ι j)).length ≤ (∑ j, (S.R (ι j)).length)+2*V := by
    have h₁ := placed_update_volume ι hι S.R (reg re) R
    have h₂ := placed_update_volume ι hι (Function.update S.R (ι (reg re)) R) (reg im) I
    have hR : R.length = V := by simp [R,replicaKeyWords,V]
    have hI : I.length = V := by simp [I,replicaKeyWords,V]
    change (∑ j, (M.R (ι j)).length) ≤ _ at h₂
    omega
  rw [hxs] at hn₄
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,(Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · omega
  · apply congrArg (mk v₄)
    rw [show List.zipWith (pairSym (prime+K)) xs ys =
      keyReplicaWords (fun r k b => pairSym (prime+K) (realBits r k b) (imagBits r k b)) from keyReplicaWords_zipWith _ _ _]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hc : i = count
    · subst i; simp
    by_cases hs : i = src
    · subst i; simp [B,hc]
    by_cases hre : i = ι (reg re)
    · subst i; simp [B,N,M,hc,hs,hblank (ι (reg re)) (by simp),hplaced.ne hne]
    by_cases him : i = ι (reg im)
    · subst i; simp [B,N,M,hc,hs,hre,hblank (ι (reg im)) (by simp)]
    · simp [B,N,M,hc,hs,hre,him]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
