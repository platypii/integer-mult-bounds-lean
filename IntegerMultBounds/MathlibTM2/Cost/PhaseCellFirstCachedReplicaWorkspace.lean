module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstCachedReplicaRecoveryStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedCouplingSharedWorkspace

/-! First-pass scratch is already contained in the recovery-preparation
allowance. Only linear row traffic is added to shared reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

theorem cachedReplicaCouplingTransitionWorkspace_le_preparation (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M : ℕ) :
    cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H M H.metadataWidth ≤
      cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M+48*(H.span*H.wordWidth)+48 := by
  have hlocal : cachedReplicaLocalCouplingWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) M
      H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth ≤
      cachedReplicaRecoveryPreparationRowWorkspace H hQ push c M := by
    unfold cachedReplicaLocalCouplingWorkspace cachedReplicaRecoveryPreparationRowWorkspace
      cachedCollectedReplicaRecoveryRhsWorkspace cachedPackedBoundaryRecoveryRhsWorkspace
      cachedPreparedSharedLocalFeedCouplingWorkspace
    omega
  unfold cachedReplicaCouplingTransitionWorkspace stageReplicaCouplingRowCost finishReplicaCouplingRowCost
  omega

theorem initializedCachedReplicaInteriorWorkspace_le_affine (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K M cV : ℕ) (hgap : H.t-s ≤ s)
    (hl : H.l = haloInverseRingLog s H.t) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M ≤
      replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cV+
      releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H M+
      H.Fs.length*(76*(H.span*H.wordWidth)+74)+56+
      replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length*(40*H.t*H.wordWidth) := by
  have hi := initializedReplicaHaloWorkspace_le_local (A := A) (U := U) H hQ R K cV hgap hl hV
  have hv := Nat.mul_le_mul_left (replicaHaloTrafficFactor (A := A) (U := U) hQ R cV*H.Fs.length)
    (replicaHaloLocalSymbolVolume_le H)
  dsimp only [initializedCachedReplicaInteriorWorkspace,cachedReplicaInteriorFinishingWorkspace,
    initializedReplicaHaloWorkspace,initializedReplicaHaloLocalWorkspace,replicaInteriorSharedWorkspace,
    allocateZeroLineCost,realReplicaRowsCost,reverseCopyRowsCost] at hi ⊢
  nlinarith only [hi,hv]

end IntegerMultBounds.MathlibTM2.Cost
