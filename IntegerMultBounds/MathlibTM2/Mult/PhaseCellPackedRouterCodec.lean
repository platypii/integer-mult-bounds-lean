module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlaneData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinBitPlanes

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A N D W : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def packedRouterPlaneInput (S : Stacks T A) (re im : Fin T)
    (realBits imagBits : Fin N → Fin D → Fin W → Bool) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R re
    (replicaKeyWords (fun r k b => bitSymbol (realBits r k b)))) im
      (replicaKeyWords (fun r k b => bitSymbol (imagBits r k b))))}

def packedRouterPlaneOutput (S : Stacks T A) (re im : Fin T)
    (realBits imagBits : Fin N → Fin D → Fin W → Bool) : Stacks T A :=
  let M := packedRouterPlaneInput S re im realBits imagBits
  {M with L := fun _ => [], R := (Function.update (Function.update M.R re
    (keyReplicaWords (fun r k b => bitSymbol (realBits r k b)))) im
      (keyReplicaWords (fun r k b => bitSymbol (imagBits r k b))))}

def packedRouterUsing (src re im tmp saved count reRev imRev : Fin T)
    (route : Pr P T Q A U) : Pr P T Q A U :=
  .seq (copyPairBitPlanes src re im tmp saved)
    (.seq route (.seq (uclear src) (joinBitPlanes count re im reRev imRev src)))

/-- A codec composition lemma. Concrete callers discharge `hroute` with their
actual routing program; final machine theorems expose no routing callback. -/
theorem packedRouterUsing_exec (src re im tmp saved count reRev imRev : Fin T)
    (hreg : [src,re,im,tmp,saved,count,reRev,imRev].Nodup) (hA : 4 ≤ A)
    (realBits imagBits : Fin N → Fin D → Fin W → Bool)
    (route : Pr P T Q A U) (routeCost : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))
    (hcount : (S.R count).length = N*(D*W))
    (hblank : ∀ i ∈ [re,im,tmp,saved,reRev,imRev], S.R i = [])
    (hroute : ∀ u : HS T Q A U, ∃ u' n, u'.user = u.user ∧ n ≤ routeCost ∧
      Exec body route (mk u (packedRouterPlaneInput S re im realBits imagBits)) n
        (mk u' (packedRouterPlaneOutput S re im realBits imagBits))) :
    let V := N*(D*W)
    ∃ v' n, v'.user = v.user ∧ n ≤ (12*V+12)+routeCost+(2*V+2)+(8*V+6) ∧
      Exec body (packedRouterUsing src re im tmp saved count reRev imRev route) (mk v S) n
        (mk v' {S with L := fun _ => [], R := (Function.update (Function.update S.R src
          (keyReplicaWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))) count [])}) := by
  dsimp only
  let V := N*(D*W)
  have hr := hreg
  regs_ne hr
  have hsrcLen : (S.R src).length = V := by simp [hsrc,replicaKeyWords,V]
  obtain ⟨v₁,hu₁,he₁⟩ := copyPairBitPlanes_exec (body := body) src re im tmp saved
    (by regs_nodup) v S (hblank tmp (by simp)) (hblank saved (by simp))
  let R := replicaKeyWords (fun r k b => (bitSymbol (realBits r k b) : Fin (A+4)))
  let I := replicaKeyWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (A+4)))
  let M := packedRouterPlaneInput S re im realBits imagBits
  have he₁' : Exec body (copyPairBitPlanes src re im tmp saved) (mk v S) (12*V+12) (mk v₁ M) := by
    rw [hsrcLen] at he₁
    simpa only [M,packedRouterPlaneInput,R,I,hsrc,hblank re (by simp),hblank im (by simp),List.append_nil,
      replicaKeyPair_real hA,replicaKeyPair_imag hA] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hroute v₁
  let RK := keyReplicaWords (fun r k b => (bitSymbol (realBits r k b) : Fin (A+4)))
  let IK := keyReplicaWords (fun r k b => (bitSymbol (imagBits r k b) : Fin (A+4)))
  let F := packedRouterPlaneOutput S re im realBits imagBits
  have hNsrc : F.R src = S.R src := by
    simp only [F,packedRouterPlaneOutput,M,packedRouterPlaneInput,Function.update_of_ne ‹src ≠ im›,Function.update_of_ne ‹src ≠ re›]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body src v₂ F
  rw [hNsrc,hsrcLen] at he₃
  let B : Stacks T (A) := {F with R := Function.update F.R src []}
  let xs := keyReplicaWords realBits
  let ys := keyReplicaWords imagBits
  have hxs : xs.length = V := by simp [xs,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have hys : ys.length = V := by simp [ys,keyReplicaWords,replicaKeyWords,V,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := joinBitPlanes_exec (body := body) count re im reRev imRev src
    (by regs_nodup) hA xs ys (hxs.trans hys.symm) v₃ B
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,hxs,V] using hcount)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,xs,RK,keyReplicaWords_map])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,ys,IK,keyReplicaWords_map])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput] using hblank reRev (by simp))
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput] using hblank imRev (by simp))
  rw [hxs] at hn₄
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,(Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · omega
  · apply congrArg (mk v₄)
    rw [show List.zipWith (pairSym (A)) xs ys =
      keyReplicaWords (fun r k b => pairSym (A) (realBits r k b) (imagBits r k b)) from keyReplicaWords_zipWith _ _ _]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hc : i = count
    · subst i; simp
    by_cases hs : i = src
    · subst i; simp [B,hc]
    by_cases hre : i = re
    · subst i; simp [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,hc,hs,hblank re (by simp),‹re ≠ im›]
    by_cases him : i = im
    · subst i; simp [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,hc,hs,hre,hblank im (by simp)]
    · simp [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,hc,hs,hre,him]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
