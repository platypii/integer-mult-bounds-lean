module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaCouplingRowsResources

/-! An exact audit of the executed baseline: shared setup is paid once, but
the scalar recovery interior bill is currently paid for every replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

noncomputable def generatedReplicaRecoverySharedTime (H : ReplicaHaloProblem s) (target : ℕ) :=
  generatedReplicaBoundaryFactoryCost H target+
    replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    initializeReplicaCouplingRuntimeCost H.metadataWidth (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span)+
    replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    4*(H.span*H.wordWidth)+initializeReplicaBoundaryRhsCost H+32

def generatedReplicaRecoveryRowTime (H : ReplicaHaloProblem s) (target : ℕ) :=
  replicaCouplingTransitionCost H H.metadataWidth+completeReplicaRowCost H target (12*H.band+1)+
    26*(H.span*H.wordWidth)+33

theorem generatedReplicaRecoveryCost_affine (H : ReplicaHaloProblem s) (target : ℕ) :
    generatedReplicaRecoveryCost H target = initializedReplicaCouplingRowsTime H+
      generatedReplicaRecoverySharedTime H target+H.Fs.length*generatedReplicaRecoveryRowTime H target := by
  unfold generatedReplicaRecoveryCost initializedReplicaInteriorRecoveryCost coupledReplicaRecoveryCallerCost
    releasedReplicaCouplingCost preparedReplicaCouplingCost releasedReplicaRecoveryCallerCost
    initializedReplicaRecoveryCallerCost replicaRecoveryCallerCost loadedReplicaRecoveryLoopCost copyRowsOrderedCost
    initializedReplicaCouplingRowsTime realInitializedReplicaHaloTime generatedReplicaRecoverySharedTime
    generatedReplicaRecoveryRowTime
  ring

/-- The baseline bill includes scalar recovery once for every replica. -/
theorem generatedReplicaRecoveryCost_scalar_recovery_charge (H : ReplicaHaloProblem s) (target : ℕ) :
    H.Fs.length*packedBoundaryRecoveryCost H.p H.u H.l target H.rhsExp s H.t H.origin (H.origin+H.span)
      H.metadataWidth H.precision H.wordWidth ≤ generatedReplicaRecoveryCost H target := by
  have hrow : packedBoundaryRecoveryCost H.p H.u H.l target H.rhsExp s H.t H.origin (H.origin+H.span)
      H.metadataWidth H.precision H.wordWidth ≤ generatedReplicaRecoveryRowTime H target := by
    unfold generatedReplicaRecoveryRowTime completeReplicaRowCost finishedReplicaRecoveryCost replicaRecoveryRowCost
    omega
  have hh := Nat.mul_le_mul_left H.Fs.length hrow
  rw [generatedReplicaRecoveryCost_affine]
  omega

end IntegerMultBounds.MathlibTM2.Cost
