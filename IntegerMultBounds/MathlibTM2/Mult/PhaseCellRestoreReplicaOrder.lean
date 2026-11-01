module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchiveAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Restore replica order by reusing the crop/archive loop on whole packets.
The extra pass is linear in local output volume and preserves packet symbols. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 14 Q A U}

/-- Ports 0/1/2 retain rows/word width/replicas; ports 6/7 are source/destination. -/
def restoreReplicaOrder : Pr P 14 Q A U :=
  .seq (unaryProduct 0 1 3 9 10)
    (.seq (ucopy 2 4 10)
      (.seq (packedCoreArchiveLoop 4 5 3 6 7 8 9 10 0 1 11 12 13) (uclear 3)))

def restoreReplicaOrderCost (N L W : ℕ) : ℕ :=
  (L*(4*W+9)+4)+(4*N+4)+(N*(packedCoreArchiveStepCost 0 L L W+3)+2)+(2*(L*W)+2)

/-- Replica-order restoration is linear in the local encoded packet volume,
including the two generated counters. -/
theorem restoreReplicaOrderCost_linear (N L W : ℕ) (hW : 1 ≤ W) :
    restoreReplicaOrderCost N L W ≤ 35*((N+1)*(L*W+1)) := by
  have hL : L ≤ L*W := by simpa using Nat.mul_le_mul_left L hW
  have hNL := Nat.mul_le_mul_left N hL
  unfold restoreReplicaOrderCost packedCoreArchiveStepCost retireCountedLineCost
  nlinarith

theorem restoreReplicaOrder_exec (q W a L : ℕ) (hfit : a+L ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4))) (v : HS 14 Q A U) (S : Stacks 14 A)
    (hrows : (S.R 0).length = L) (hwidth : (S.R 1).length = W) (hreplicas : (S.R 2).length = Ds.length)
    (hblank : ∀ k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13]), S.R k = [])
    (hsrc : S.R 6 = (Ds.map (fun D => cstream A W (packedInterval a L D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
      (packedIntervalRead q W a (cstream A W (packedInterval a L D)++tail)) z ε) Zs Ds) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoreReplicaOrderCost Ds.length L W ∧
      Exec body restoreReplicaOrder (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R 6 tail) 7
          ((Ds.reverse.map (fun D => cstream A W (packedInterval a L D))).flatten++S.R 7))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
        (packedIntervalRead q W a (cstream A W (packedInterval a L D)++S.R 7)) z ε) Zs.reverse Ds.reverse := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show ([(0 : Fin 14),1,3,9,10]).Nodup by decide) v S (hblank 9 (by simp)) (hblank 10 (by simp))
  let F : Stacks 14 A := {S with R := Function.update S.R 3 (List.replicate (L*W) tick)}
  have he₁' : Exec body (unaryProduct 0 1 3 9 10) (Host.mk v S) n₁ (Host.mk v₁ F) := by
    simpa [F,hrows,hwidth,hblank 3 (by simp)] using he₁
  have hn₁' : n₁ ≤ L*(4*W+9)+4 := by simpa only [hrows,hwidth] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 2) (b := 4) (t := 10)
    (by decide) (by decide) (by decide) v₁ F (by simp [F,hblank 10 (by simp)])
  let G : Stacks 14 A := {F with R := Function.update F.R 4 (List.replicate Ds.length tick)}
  have he₂' : Exec body (ucopy 2 4 10) (Host.mk v₁ F) (4*Ds.length+4) (Host.mk v₂ G) := by
    simpa [G,F,hreplicas,hblank 4 (by simp)] using he₂
  obtain ⟨v₃,H,n₃,hu₃,hn₃,he₃,hs,hd,hc,hI,hO,hL,hframe,haccuracy⟩ := packedCoreArchiveLoop_interval_accurate_exec
    (body := body) 4 5 3 6 7 8 9 10 0 1 11 12 13 (by decide) v₂ G q W a L 0 L hfit (by omega)
    Zs Ds ε tail hgood (by simpa [G,F] using hsrc) (by simp [G])
    (by simp [G,F,hblank 5 (by simp)]) (by simp [G,F])
    (by simpa [G,F] using hrows) (by simpa [G,F] using hwidth)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [G,F,hblank 8 (by simp),hblank 9 (by simp),hblank 10 (by simp),
        hblank 11 (by simp),hblank 12 (by simp),hblank 13 (by simp)])
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 3 v₃ H
  have h3 : (H.R 3).length = L*W := by
    rw [hframe 3 (by decide) (by decide) (by decide)]
    simp [G,F]
  have hfinal : {H with R := Function.update H.R 3 []} =
      {S with R := (Function.update (Function.update S.R 6 tail) 7
        ((Ds.reverse.map (fun D => cstream A W (packedInterval a L D))).flatten++S.R 7))} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    funext k
    change Function.update H.R 3 [] k = Function.update (Function.update S.R 6 tail) 7 _ k
    by_cases hk : k = 3
    · subst k; simp [hblank 3 (by simp)]
    · rw [Function.update_of_ne hk]
      by_cases hsrc' : k = 6
      · subst k; simpa using hs
      · by_cases hdst' : k = 7
        · subst k; simpa [G,F] using hd
        · rw [Function.update_of_ne hdst',Function.update_of_ne hsrc']
          by_cases hclock : k = 4
          · subst k; simpa [hblank 4 (by simp)] using hc
          · rw [hframe k hsrc' hdst' hclock]
            simp [G,F,Function.update_of_ne hclock,Function.update_of_ne hk]
  rw [h3,hfinal] at he₄
  refine ⟨v₄,n₁+((4*Ds.length+4)+(n₃+(2*(L*W)+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄)),?_⟩
  · unfold restoreReplicaOrderCost
    omega
  · simpa [G,F] using haccuracy

omit [NeZero s] in
theorem restoreReplicaOrder_native :
    mnNativePushBound 2 (restoreReplicaOrder (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨?_,?_,packedCoreArchiveLoop_interval_native _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  all_goals simp [unaryProduct,ucopy,umulSym,uclear,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

omit [NeZero s] in
theorem restoreReplicaOrder_within_stock {v v' : HS 14 Q A U} {S F : Stacks 14 A} {n N L W : ℕ}
    (hex : Exec body restoreReplicaOrder (Host.mk v S) n (Host.mk v' F))
    (hn : n ≤ restoreReplicaOrderCost N L W) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*restoreReplicaOrderCost N L W)
      depth restoreReplicaOrder (Host.mk v S) n (Host.mk v' F) :=
  mn_native_exec_within hex 2 restoreReplicaOrder_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
