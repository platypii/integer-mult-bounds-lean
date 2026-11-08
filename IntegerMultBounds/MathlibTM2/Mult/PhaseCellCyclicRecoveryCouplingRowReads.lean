module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingRow

/-! Exact stream endpoints of paired recovery, derived from the two structural
piece frames. No concrete tape-bank equality or finite case enumeration is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "source" => CyclicRecoveryPlacement.bank 132
variable {s T A : ℕ} [NeZero s]

omit [NeZero s] in
theorem jointSourceRecoveryCouplingState_reads (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (src : Fin T) (hbank : ∀ i, placement.bank i ≠ src) (hgather : ∀ i, plan.gather i ≠ src)
    (C : ZMod s → GaussianInt) (tail rhs output : List (Fin (A+4))) (S : Stacks T A) :
    let F := jointSourceRecoveryCouplingState H placement src C tail rhs output S
    F.R src = tail ∧ F.R (placement.bank 93) = rhs ∧
      F.R (placement.bank 110) = output++S.R (placement.bank 110) ∧
      F.R (plan.gather 125) = cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (plan.gather 125) := by
  dsimp only
  rw [jointSourceRecoveryCouplingState_eq H placement src hbank hgather]
  simp [hbank,hgather,(hbank 93).symm,(hbank 110).symm,(hgather 125).symm,
    placement.bank_injective.eq_iff,placement.bank_gather_disjoint]

theorem cyclicRecoveryCouplingRowState_reads (H K : ReplicaHaloProblem s)
    (C D : ZMod s → GaussianInt) (tail rhsL rhsR outputL outputR : List (Fin (A+4))) (S : Stacks 840 A) :
    let F := cyclicRecoveryCouplingRowState H K C D tail rhsL rhsR outputL outputR S
    F.R source = tail ∧
      F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = rhsL ∧
      F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = rhsR ∧
      F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110) = outputL++S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110) ∧
      F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110) = outputR++S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110) ∧
      F.R (CyclicRecoveryPlacement.leftJob.plan.gather 125) = cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (CyclicRecoveryPlacement.leftJob.plan.gather 125) ∧
      F.R (CyclicRecoveryPlacement.rightJob.plan.gather 125) = cstream A K.wordWidth (packedInterval K.origin K.span D)++S.R (CyclicRecoveryPlacement.rightJob.plan.gather 125) := by
  dsimp only
  let J := jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C
    (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  have hl := jointSourceRecoveryCouplingState_reads H CyclicRecoveryPlacement.leftJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i)) C (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  have hr := jointSourceRecoveryCouplingState_reads K CyclicRecoveryPlacement.rightJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.gather i)) D tail rhsR outputR J
  refine ⟨hr.1,?_,hr.2.1,?_,?_,?_,?_⟩
  · exact (cyclicRecoveryRightPiece_frame K D tail rhsR outputR J _ (.bank 93)).trans hl.2.1
  · exact (cyclicRecoveryRightPiece_frame K D tail rhsR outputR J _ (.bank 110)).trans hl.2.2.1
  · exact hr.2.2.1.trans (congrArg (fun xs => outputR++xs)
      (cyclicRecoveryLeftPiece_frame H C (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S _ (.bank 110)))
  · exact (cyclicRecoveryRightPiece_frame K D tail rhsR outputR J _ (.gather 125)).trans hl.2.2.2
  · exact hr.2.2.2.trans (congrArg (fun xs => cstream A K.wordWidth (packedInterval K.origin K.span D)++xs)
      (cyclicRecoveryLeftPiece_frame H C (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S _ (.gather 125)))

theorem cyclicRecoveryCouplingRowState_frame (H K : ReplicaHaloProblem s)
    (C D : ZMod s → GaussianInt) (tail rhsL rhsR outputL outputR : List (Fin (A+4))) (S : Stacks 840 A)
    (k : Fin 840) (hs : k ≠ source)
    (hL93 : k ≠ CyclicRecoveryPlacement.leftJob.coupling.bank 93)
    (hL110 : k ≠ CyclicRecoveryPlacement.leftJob.coupling.bank 110)
    (hL125 : k ≠ CyclicRecoveryPlacement.leftJob.plan.gather 125)
    (hR93 : k ≠ CyclicRecoveryPlacement.rightJob.coupling.bank 93)
    (hR110 : k ≠ CyclicRecoveryPlacement.rightJob.coupling.bank 110)
    (hR125 : k ≠ CyclicRecoveryPlacement.rightJob.plan.gather 125) :
    (cyclicRecoveryCouplingRowState H K C D tail rhsL rhsR outputL outputR S).R k = S.R k := by
  let J := jointSourceRecoveryCouplingState H CyclicRecoveryPlacement.leftJob.coupling source C
    (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S
  have hr := jointSourceRecoveryCouplingState_frame K CyclicRecoveryPlacement.rightJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_right_disjoint _ (.gather i)) D tail rhsR outputR J k hs hR93 hR110 hR125
  have hl := jointSourceRecoveryCouplingState_frame H CyclicRecoveryPlacement.leftJob.coupling source
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.bank i))
    (fun i => CyclicRecoveryPlacement.source_left_disjoint _ (.gather i)) C (cstream A K.wordWidth (packedInterval K.origin K.span D)++tail) rhsL outputL S k hs hL93 hL110 hL125
  exact hr.trans hl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
