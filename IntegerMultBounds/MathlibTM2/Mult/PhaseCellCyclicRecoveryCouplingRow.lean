module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryJobs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJointSourceRecoveryCoupling

/-! One joint boundary row feeds both retained recovery banks in source order.
Each piece keeps the other's cache and headers, without deinterleaving queues. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "source" => CyclicRecoveryPlacement.bank 132
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

noncomputable def cyclicRecoveryCouplingRow (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  .seq (jointSourceRecoveryCoupling CyclicRecoveryPlacement.leftJob.coupling source hQ)
    (jointSourceRecoveryCoupling CyclicRecoveryPlacement.rightJob.coupling source hQ)

def cyclicRecoveryCouplingPieceCost (H : ReplicaHaloProblem s) : ℕ :=
  (6*(H.span*H.wordWidth)+6)+(cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6))

noncomputable def cyclicRecoveryCouplingPieceWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) : ℕ :=
  2*(6*(H.span*H.wordWidth)+6)+
    (cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ+2*(6*(H.span*H.wordWidth)+6))

def cyclicRecoveryCouplingRowState (H K : ReplicaHaloProblem s)
    (C D : ZMod s → GaussianInt) (tail rhsL rhsR outputL outputR : List (Fin (A+4)))
    (S : Stacks 840 A) : Stacks 840 A :=
  let F := jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C
    (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  jointSourceRecoveryCouplingState K CyclicRecoveryPlacement.rightJob.coupling source D tail rhsR outputR F

theorem cyclicRecoveryLeftPiece_frame (H : ReplicaHaloProblem s) (C : ZMod s → GaussianInt)
    (tail rhs output : List (Fin (A+4))) (S : Stacks 840 A) (k : Fin 840) (hk : CyclicRecoveryPlacement.rightJob.Owns k) :
    (jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C tail rhs output S).R k = S.R k := by
  have hoff (i : Fin 840) (hi : CyclicRecoveryPlacement.leftJob.Owns i) : k ≠ i := by
    intro he
    apply CyclicRecoveryPlacement.jobs_disjoint i hi
    rw [← he]
    exact hk
  exact jointSourceRecoveryCouplingState_frame H CyclicRecoveryPlacement.leftJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i)) C tail rhs output S k
    (CyclicRecoveryPlacement.source_right_disjoint k hk)
    (hoff _ (.bank 93)) (hoff _ (.bank 110)) (hoff _ (.gather 125))

theorem cyclicRecoveryRightPiece_frame (K : ReplicaHaloProblem s) (D : ZMod s → GaussianInt)
    (tail rhs output : List (Fin (A+4))) (S : Stacks 840 A) (k : Fin 840) (hk : CyclicRecoveryPlacement.leftJob.Owns k) :
    (jointSourceRecoveryCouplingState K CyclicRecoveryPlacement.rightJob.coupling source D tail rhs output S).R k = S.R k := by
  have hoff (i : Fin 840) (hi : CyclicRecoveryPlacement.rightJob.Owns i) : k ≠ i := by
    intro he
    apply CyclicRecoveryPlacement.jobs_disjoint k hk
    rw [he]
    exact hi
  exact jointSourceRecoveryCouplingState_frame K CyclicRecoveryPlacement.rightJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.gather i)) D tail rhs output S k
    (CyclicRecoveryPlacement.source_left_disjoint k hk)
    (hoff _ (.bank 93)) (hoff _ (.bank 110)) (hoff _ (.gather 125))

theorem cyclicRecoveryCouplingRow_exec_within (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (C D B E : ZMod s → GaussianInt)
    (hC : ∀ j, Fits H.wordWidth (C j)) (hD : ∀ j, Fits K.wordWidth (D j))
    (tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4)))
    (v : HS 840 Q A U) (S : Stacks 840 A)
    (headersL : ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL S)
    (headersR : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR S)
    (cacheL : CachedRecoveryCouplingReady H rawL pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank S))
    (cacheR : CachedRecoveryCouplingReady K rawR pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank S))
    (hsource : S.R source = cstream A H.wordWidth (packedInterval H.origin H.span C)++
      (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail))
    (hrhsL : S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsL)
    (hrhsR : S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = cstream A K.wordWidth (packedInterval K.origin K.span E)++rhsR)
    (depth : ℕ) :
    let outputL := cstream A H.wordWidth (packedInterval H.origin H.span
      (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) true C B))
    let outputR := cstream A K.wordWidth (packedInterval K.origin K.span
      (guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band K.origin (K.origin+K.span) true D E))
    let F := cyclicRecoveryCouplingRowState H K C D tail rhsL rhsR outputL outputR S
    ∃ vf m, vf.user = v.user ∧ m ≤ cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
          cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ))
        depth (cyclicRecoveryCouplingRow hQ) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL F ∧
      ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR F ∧
      CachedRecoveryCouplingReady H (outputL++rawL) pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank F) ∧
      CachedRecoveryCouplingReady K (outputR++rawR) pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank F) := by
  dsimp only
  let outputL := cstream A H.wordWidth (packedInterval H.origin H.span
    (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) true C B))
  let outputR := cstream A K.wordWidth (packedInterval K.origin K.span
    (guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band K.origin (K.origin+K.span) true D E))
  let J := jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C
    (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  obtain ⟨vi,mi,hu₁,hm₁,he₁,hhL,hcL⟩ := jointSourceRecoveryCoupling_exec_within (body := body)
    H CyclicRecoveryPlacement.leftJob.coupling source (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i)) hQ hA hsepL buffersL C B hC
    _ rhsL rawL pageL v S headersL cacheL hsource hrhsL depth
  have hframe (k : Fin 840) (hk : CyclicRecoveryPlacement.rightJob.Owns k) : J.R k = S.R k :=
    cyclicRecoveryLeftPiece_frame H C _ rhsL outputL S k hk
  have hheaders : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR J := by
    apply headersR.of_frame K CyclicRecoveryPlacement.rightJob.plan.gather buffersR S J
    intro i; exact hframe _ (.gather i)
  have hview : embStk CyclicRecoveryPlacement.rightJob.coupling.bank J = embStk CyclicRecoveryPlacement.rightJob.coupling.bank S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i; exact hframe _ (.bank i)
  have hsrcJ : J.R source = cstream A K.wordWidth (packedInterval K.origin K.span D)++tail := by
    dsimp only [J]
    rw [jointSourceRecoveryCouplingState_eq H CyclicRecoveryPlacement.leftJob.coupling source
      (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
      (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i))]
    simp [(CyclicRecoveryPlacement.source_left_disjoint _ (.bank 93)).symm,
      (CyclicRecoveryPlacement.source_left_disjoint _ (.bank 110)).symm,
      (CyclicRecoveryPlacement.source_left_disjoint _ (.gather 125)).symm]
  obtain ⟨vf,mf,hu₂,hm₂,he₂,hhR,hcR⟩ := jointSourceRecoveryCoupling_exec_within (body := body)
    K CyclicRecoveryPlacement.rightJob.coupling source (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.gather i)) hQ hA hsepR buffersR D E hD
    tail rhsR rawR pageR vi J hheaders (hview ▸ cacheR) hsrcJ ((hframe _ (.bank 93)).trans hrhsR) depth
  refine ⟨vf,mi+mf,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_,?_,hhR,?_,hcR⟩
  · exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂
  · apply hhL.of_frame H CyclicRecoveryPlacement.leftJob.plan.gather buffersL J
    intro i; exact cyclicRecoveryRightPiece_frame K D tail rhsR outputR J _ (.gather i)
  · have hleftView : embStk CyclicRecoveryPlacement.leftJob.coupling.bank
        (jointSourceRecoveryCouplingState K CyclicRecoveryPlacement.rightJob.coupling source D tail rhsR outputR J) =
        embStk CyclicRecoveryPlacement.leftJob.coupling.bank J := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i; exact cyclicRecoveryRightPiece_frame K D tail rhsR outputR J _ (.bank i)
    exact hleftView.symm ▸ hcL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
