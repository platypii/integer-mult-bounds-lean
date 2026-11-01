module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryNumericalFast

/-! Retained coupling's native setup and traffic do not contain numerical row multiplication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem retainedCouplingIntervalNativeCost_le (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) (hw : 1 ≤ w) (hqw : q ≤ w) :
    retainedCouplingIntervalNativeCost boundary P q w s t u band a b origin N V ≤
      prepareCost q w+10000*(N+band+1)*(w+V+tblC V 1+1)+
        1000*((couplingCoefficientPageInterval P q s t u band a b origin N).length+1)*(w+1) := by
  have hsplit := preparedSharedLocalFeedCouplingIntervalCost_split boundary P q w s t u band a b origin N V
  have htop := (Schoenhage.Schedule.topN_facts hw).2.1
  unfold preparedSharedLocalFeedCouplingIntervalCost maskCouplingSourceCost transferCountedLineCost at hsplit
  ring_nf at hsplit ⊢
  omega

theorem replicaRecoveryPreparationNativeCost_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaRecoveryPreparationNativeCost H ≤ prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*
        (H.wordWidth+H.metadataWidth+tblC H.metadataWidth 1+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1) := by
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hqw : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hnative := retainedCouplingIntervalNativeCost_le true (2^15*H.p) H.precision H.wordWidth s H.t H.u
    H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth hw hqw
  unfold replicaRecoveryPreparationNativeCost replicaBoundaryRhsCost stageReplicaBoundaryRhsCost
    replicaRecoveryInputsCost packedBoundaryRecoveryInputsCost packedBoundaryRecoveryFieldCost
    packedRecoveryRhsInputCost moveCountedLineCost generatedBoundaryUnfoldCost
    packedRecoveryDestinationCost retireCountedLineCost copyCountedLineCost
  ring_nf at hnative ⊢
  omega

end IntegerMultBounds.MathlibTM2.Cost
