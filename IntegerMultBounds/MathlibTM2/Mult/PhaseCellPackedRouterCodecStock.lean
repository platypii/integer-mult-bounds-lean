module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRouterCodec
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Linear codec work surrounds an arbitrary bounded router; recursive routing
keeps its own workspace certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A N D W : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem copyPairBitPlanes_native (src re im tmp saved : Fin T) :
    mnNativePushBound 2 (copyPairBitPlanes (P := P) (Q := Q) (A := A) (U := U) src re im tmp saved) := by
  simp [copyPairBitPlanes,copyMappedWords,copyR,copyStep,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem joinBitPlanes_native (count re im reRev imRev dst : Fin T) :
    mnNativePushBound 1 (joinBitPlanes (P := P) (Q := Q) (A := A) (U := U) count re im reRev imRev dst) := by
  simp [joinBitPlanes,pairComponents,countedLoop,countedLoopBody,pairComponentStep,
    moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem packedRouterUsing_exec_within (src re im tmp saved count reRev imRev : Fin T)
    (hreg : [src,re,im,tmp,saved,count,reRev,imRev].Nodup) (hA : 4 ≤ A)
    (realBits imagBits : Fin N → Fin D → Fin W → Bool)
    (route : Pr P T Q A U) (routeCost routeStock depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))
    (hcount : (S.R count).length = N*(D*W))
    (hblank : ∀ i ∈ [re,im,tmp,saved,reRev,imRev], S.R i = [])
    (hroute : ∀ u : HS T Q A U, ∃ u' n, u'.user = u.user ∧ n ≤ routeCost ∧
      ExecWithin body (fun z c => mnSize c+z ≤
        mnSize (mk u (packedRouterPlaneInput S re im realBits imagBits))+depth+routeStock) depth route (mk u (packedRouterPlaneInput S re im realBits imagBits)) n
        (mk u' (packedRouterPlaneOutput S re im realBits imagBits))) :
    let V := N*(D*W)
    ∃ v' n, v'.user = v.user ∧ n ≤ (12*V+12)+routeCost+(2*V+2)+(8*V+6) ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        2*(12*V+12)+routeStock+(8*V+6)) depth (packedRouterUsing src re im tmp saved count reRev imRev route) (mk v S) n
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
    simp only [F,packedRouterPlaneOutput,packedRouterPlaneInput,Function.update_of_ne ‹src ≠ im›,Function.update_of_ne ‹src ≠ re›]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body src v₂ F
  rw [hNsrc,hsrcLen] at he₃
  let B : Stacks T (A) := {F with R := Function.update F.R src []}
  let xs := keyReplicaWords realBits
  let ys := keyReplicaWords imagBits
  have hxs : xs.length = V := by simp [xs,keyReplicaWords,replicaKeyWords,V,Nat.mul_left_comm]
  have hys : ys.length = V := by simp [ys,keyReplicaWords,replicaKeyWords,V,Nat.mul_left_comm]
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := joinBitPlanes_exec (body := body) count re im reRev imRev src
    (by regs_nodup) hA xs ys (hxs.trans hys.symm) v₃ B
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput,hxs,V] using hcount)
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,packedRouterPlaneInput,xs,keyReplicaWords_map])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,packedRouterPlaneInput,ys,keyReplicaWords_map])
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput] using hblank reRev (by simp))
    (by simpa (disch := first | assumption | (apply Ne.symm; assumption)) [B,F,packedRouterPlaneOutput,M,packedRouterPlaneInput] using hblank imRev (by simp))
  rw [hxs] at hn₄
  let bound := mnSize (mk v S)+depth+2*(12*V+12)+routeStock+(8*V+6)
  have hw₁ := mn_native_exec_within he₁' 2 (copyPairBitPlanes_native src re im tmp saved)
    depth (mnSize (mk v S)+depth+2*(12*V+12)) (le_refl _)
  have hsetup := hw₁.final
  have hw₁' := hw₁.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    dsimp only [bound]
    omega)
  have hw₂ := he₂.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    change mnSize c+z ≤ mnSize (mk v₁ M)+depth+routeStock at hc
    dsimp only [bound]
    omega)
  have hw₃ := mn_native_exec_within he₃ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
    depth bound (by
      have hh := hw₂.final
      change mnSize (mk v₂ F)+depth ≤ bound at hh
      simpa only [Nat.zero_mul,Nat.add_zero] using hh)
  have hw₄ := mn_native_exec_within he₄ 1 (joinBitPlanes_native count re im reRev imRev src)
    depth bound (by
      have hh := hw₂.final
      have hs := (mn_native_exec_within he₃ 0
        (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
        depth (mnSize (mk v₂ F)+depth) (by omega)).final
      change mnSize (mk v₃ B)+depth ≤ mnSize (mk v₂ F)+depth at hs
      have hr := he₂.final
      change mnSize (mk v₂ F)+depth ≤ mnSize (mk v₁ M)+depth+routeStock at hr
      dsimp only [bound]
      omega)
  have hwhole := ExecWithin.seq hw₁' (ExecWithin.seq hw₂ (ExecWithin.seq hw₃ hw₄))
  obtain ⟨vf,n,hu,hn,he⟩ := packedRouterUsing_exec src re im tmp saved count reRev imRev hreg hA
    realBits imagBits route routeCost v S hsrc hcount hblank (by
      intro u
      obtain ⟨u',n,hu,hn,he⟩ := hroute u
      exact ⟨u',n,hu,hn,he.toExec⟩)
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique he
  rw [hsteps,hfinal] at hwhole
  exact ⟨vf,n,hu,hn,hwhole⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
