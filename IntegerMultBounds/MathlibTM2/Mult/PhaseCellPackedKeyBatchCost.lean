module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyRealBatch

/-! Separate the actual packed key bill into one setup and a local per-RHS bill.
The zero-replica bill includes all initialization and final disposal; it is an
accounting constant and does not require executing an empty numerical batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedInputConversionCost_affine (W w d N : ℕ) :
    packedInputConversionCost W w d N =
      packedInputConversionCost W w d 0+N*(4*W+8*w+4*d+28) := by
  simp only [packedInputConversionCost]
  ring

/-- Conversion and local loading are proportional to the halo length, not the
ambient period. Header preparation is charged once. -/
def packedKeyInputReplicaCost (q W L d : ℕ) : ℕ :=
  12*(L*W)+9+L*(4*W+8*(2*q+8)+4*d+28)

theorem packedKeyInputCost_affine (p q W N L : ℕ) :
    packedKeyInputCost p q W N L = packedKeyInputCost p q W 0 L+
      N*packedKeyInputReplicaCost q W L (q-p-1) := by
  simp only [packedKeyInputCost,packedInputConversionCost,packedKeyInputReplicaCost]
  ring

namespace ScalarPlacement

def packedHaloBatchHeaderCost (q w V core radius : ℕ) : ℕ :=
  prepareCoreDimensionsCost V (core+2*radius) radius+2*V+8*q+2*w+
    2*(radius+core)+packedCoreBatchPublicationCost 0 radius core w+24

/-- Identify the one-time supplier charge already used by the local solver.
The added bill contains only batch headers and owned-core publication controls. -/
theorem packedHaloBatchCostFromSetup_zero
    (p u l s t a b V finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s] :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let boundaryTarget := boundaryRecoveryTarget p finalTarget
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0 =
      packedHaloSetupReleaseCost true p u l finalTarget rhsExp s t a b V+
        packedHaloBatchHeaderCost q w V (coreLength s coreWidth k) radius := by
  simp only [packedHaloBatchCostFromSetup,packedHaloSetupReleaseCost,packedHaloBatchHeaderCost,
    packedHaloBatchCost,ite_true,Nat.zero_mul,Nat.add_zero]
  ring

theorem packedCoreBatchPublicationCost_affine (N radius core w : ℕ) :
    packedCoreBatchPublicationCost N radius core w =
      packedCoreBatchPublicationCost 0 radius core w+
        N*(packedCoreArchiveStepCost radius core (core+2*radius) w+7) := by
  simp only [packedCoreBatchPublicationCost,packedCoreArchiveControlsCost]
  ring

/-- Numerical work and cropping for one RHS. Factors and geometry are absent:
their construction and release occur in the zero-replica batch bill. -/
noncomputable def packedHaloBatchReplicaCost
    (p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  packedFreshOutputCost V (b-a) w+
    packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V+
    packedCoreArchiveStepCost radius (coreLength s coreWidth k)
      (coreLength s coreWidth k+2*radius) w+14

theorem packedHaloBatchCostFromSetup_affine
    (p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N : ℕ) [NeZero s] :
    packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N =
      packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        N*packedHaloBatchReplicaCost p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius := by
  simp only [packedHaloBatchCostFromSetup,packedHaloBatchReplicaCost,
    packedHaloBatchCost,packedCoreBatchPublicationCost,packedCoreArchiveControlsCost]
  ring

/-- The exact bill in `packedKeyRealBatch_exec`, including native count setup. -/
noncomputable def packedKeyRealBatchCost
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N : ℕ) [NeZero s] : ℕ :=
  packedKeyInputCost p q W N (b-a)+(4*N+4)+
    packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N

noncomputable def packedKeyRealBatchReplicaCost
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s] : ℕ :=
  packedKeyInputReplicaCost q W (b-a) (q-p-1)+4+
    packedHaloBatchReplicaCost p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius

theorem packedKeyRealBatchCost_affine
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N : ℕ) [NeZero s] :
    packedKeyRealBatchCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N =
      packedKeyRealBatchCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        N*packedKeyRealBatchReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius := by
  unfold packedKeyRealBatchCost packedKeyRealBatchReplicaCost
  rw [packedKeyInputCost_affine p q W N (b-a),
    packedHaloBatchCostFromSetup_affine p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N]
  ring

/-- Splitting complex inputs into a single batch doubles only the RHS charge. -/
theorem packedKeyRealBatchCost_two_components
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius N : ℕ) [NeZero s] :
    packedKeyRealBatchCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*N) =
      packedKeyRealBatchCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        N*(2*packedKeyRealBatchReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius) := by
  rw [packedKeyRealBatchCost_affine]
  ring

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
