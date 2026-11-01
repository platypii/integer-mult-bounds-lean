module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNativeGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaRecoveryPreparationRow

/-! Cached recovery pays linear stream traffic per replica; geometry table evaluation is shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedPreparedSharedLocalFeedCouplingIntervalCost_le (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) (hw : 1 ≤ w) (hqw : q ≤ w) :
    cachedPreparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V ≤
      prepareCost q w+10000*(N+band+1)*(w+V+1)+
        1000*((couplingCoefficientPageInterval P q s t u band a b origin N).length+1)*(w+1)+
        retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N := by
  have htop := (Schoenhage.Schedule.topN_facts hw).2.1
  unfold cachedPreparedSharedLocalFeedCouplingIntervalCost cachedGatheredRibbonCost
    maskCouplingSourceCost transferCountedLineCost
  ring_nf at htop ⊢
  omega

theorem cachedReplicaRecoveryPreparationRowCost_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    cachedReplicaRecoveryPreparationRowCost H ≤
      preparedResidualSolveCost H.precision H.wordWidth
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)+
      prepareCost H.precision H.wordWidth+
      20000*(H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*
        (H.wordWidth+H.metadataWidth+1)+
      1000*((couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length+1)*(H.wordWidth+1)+
      retainedPageSpatialIntervalLoopCost true H.precision H.wordWidth s H.t H.band
        H.origin (H.origin+H.span) H.origin H.span := by
  have hw : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hqw : H.precision ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hnative := cachedPreparedSharedLocalFeedCouplingIntervalCost_le true (2^15*H.p)
    H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth hw hqw
  unfold cachedReplicaRecoveryPreparationRowCost cachedCollectedReplicaRecoveryRhsCost
    cachedReplicaRecoveryRhsCost replicaBoundaryRhsCost stageReplicaBoundaryRhsCost
    replicaRecoveryInputsCost packedBoundaryRecoveryInputsCost packedBoundaryRecoveryFieldCost
    packedRecoveryRhsInputCost moveCountedLineCost generatedBoundaryUnfoldCost
    packedRecoveryDestinationCost retireCountedLineCost copyCountedLineCost
  ring_nf at hnative ⊢
  omega

/-- Cached native traffic has the same sparse halo volume as numerical recovery. -/
theorem cachedReplicaRecoveryPreparationRowCost_gap {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    cachedReplicaRecoveryPreparationRowCost H ≤
      preparedResidualSolveCost H.precision H.wordWidth
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)+
      prepareCost H.precision H.wordWidth+
      300000*(H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+1)+
      retainedPageSpatialIntervalLoopCost true H.precision H.wordWidth s H.t H.band
        H.origin (H.origin+H.span) H.origin H.span := by
  let G := H.t+(H.t-s)*H.band^2
  let W := H.wordWidth+H.metadataWidth+1
  have ht : 1 ≤ H.t := by have := NeZero.pos s; have := H.s_lt_t; omega
  have htG : H.t ≤ G := Nat.le_add_right _ _
  have hG : 1 ≤ G := ht.trans htG
  have hcard : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
    simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ
  have hrow : H.span+H.band+(haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1 ≤ 4*G := by
    have := H.span_fit
    have hband : H.band ≤ s := H.band_fit
    have := H.s_lt_t
    omega
  have hpage := couplingCoefficientPageInterval_length_geometry H.s_lt_t (2^15*H.p) H.precision H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hvolume := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span) H.s_lt_t
    (NLogN.PhaseCellBand.width_pos H.p H.u)
  have howned : (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1) ≤
      familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by unfold familyKernelVolume; omega
  have hlength : (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span).length+1 ≤ 201*G := by
    have hh := hpage.trans (howned.trans hvolume)
    change _ ≤ 200*G at hh
    omega
  have hwidth : H.wordWidth+1 ≤ W := by dsimp only [W]; omega
  let C := preparedResidualSolveCost H.precision H.wordWidth
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1)
  let L := retainedPageSpatialIntervalLoopCost true H.precision H.wordWidth s H.t H.band
    H.origin (H.origin+H.span) H.origin H.span
  calc
    _ ≤ _ := cachedReplicaRecoveryPreparationRowCost_le H
    _ ≤ C+prepareCost H.precision H.wordWidth+20000*(4*G)*W+1000*(201*G)*W+L := by gcongr
    _ ≤ _ := by dsimp only [G,W]; nlinarith only [Nat.zero_le ((H.t+(H.t-s)*H.band^2)*(H.wordWidth+H.metadataWidth+1))]


end IntegerMultBounds.MathlibTM2.Cost
