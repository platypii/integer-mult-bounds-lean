module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexLineCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingPassCost

/-! Expose both actual halo-interior passes before applying their geometry ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def realInteriorResidualOverhead (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  initializeInteriorOutputCost q s+installCouplingHeadersCost (2^15*p) q s t u band a b+
    feedCouplingPassCost false (2^15*p) q w s t u band a b+
    releaseCouplingHeadersCost (2^15*p) q s t u band a b+realResidualProjectionCost q s

theorem realInteriorResidualCost_split (p l s t u target rhsExp a b : ℕ) :
    realInteriorResidualCost p l s t u target rhsExp a b =
      solveHaloInteriorCost p l s t u target rhsExp a b+
        realInteriorResidualOverhead p l s t u target rhsExp a b := by
  dsimp only [realInteriorResidualCost,restoredInteriorResidualCost,initializedInteriorResidualCost,
    interiorResidualCost,interiorForCouplingCost,realInteriorResidualOverhead]
  ring

theorem realInteriorResidualCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b : ℕ) :
    realInteriorResidualCost p l s t u target rhsExp a b ≤
      haloInteriorCostBound p l s t u target rhsExp a b+
        realInteriorResidualOverhead p l s t u target rhsExp a b := by
  rw [realInteriorResidualCost_split]
  exact Nat.add_le_add_right (solveHaloInteriorCost_le hst p l u target rhsExp a b) _

def recoveryToleranceOverhead (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let stageTarget := recoveryTarget p target
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p stageTarget rhsExp boundaryExp countExp) rhsExp
  let recoveryExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  retireAmbientSourceCost q s+restoredCouplingPassCost true (2^15*p) q s t u (PhaseCellBand.width p u) a b+
    initializeInteriorOutputCost (executionPrecision p l stageTarget recoveryExp) s+
    publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

theorem recoveryToleranceCost_split (p l s t u target rhsExp a b : ℕ) :
    recoveryToleranceCost p l s t u target rhsExp a b =
      solveHaloInteriorCost p l s t u (recoveryTarget p target)
        (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) a b+
      recoveryToleranceOverhead p l s t u target rhsExp a b := by
  dsimp only [recoveryToleranceCost,recoveryPublishedHaloCost,recoveryInteriorCost,initializedInteriorCost,
    recoveryToleranceOverhead]
  ring

theorem recoveryToleranceCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b : ℕ) :
    recoveryToleranceCost p l s t u target rhsExp a b ≤
      haloInteriorCostBound p l s t u (recoveryTarget p target)
        (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) a b+
      recoveryToleranceOverhead p l s t u target rhsExp a b := by
  rw [recoveryToleranceCost_split]
  exact Nat.add_le_add_right (solveHaloInteriorCost_le hst p l u (recoveryTarget p target)
    (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) a b) _

def recoveryToleranceGuardedOverhead (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  let stageTarget := recoveryTarget p target
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p stageTarget rhsExp boundaryExp countExp) rhsExp
  let recoveryExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  let band := PhaseCellBand.width p u
  retireAmbientSourceCost q s+spatialCouplingRecoveryCostBound (2^15*p) q (2*q+8) s t u band a b+
    installCouplingHeadersCost (2^15*p) q s t u band a b+releaseCouplingHeadersCost (2^15*p) q s t u band a b+
    50*s*(2*q+8)+27*s+50+
    initializeInteriorOutputCost (executionPrecision p l stageTarget recoveryExp) s+
    publishHaloCost (2^15*p) q s t u band a b

theorem recoveryToleranceOverhead_guarded_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b : ℕ) (hb : b ≤ s) :
    recoveryToleranceOverhead p l s t u target rhsExp a b ≤
      recoveryToleranceGuardedOverhead p l s t u target rhsExp a b := by
  let q := executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp
    (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp
  have h := restoredCouplingPassCost_recovery_le hst (2^15*p) q u (PhaseCellBand.width p u) a b hb
  dsimp only [recoveryToleranceOverhead,recoveryToleranceGuardedOverhead]
  dsimp only [q] at h
  omega

noncomputable def sharedComplexBatchGeometryLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let initialTarget := initialSchurTarget p u bits 2
  let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  let q := executionPrecision p l initialTarget 2
  let w := executionWidth p l initialTarget 2
  let V := publicationGeometryWidth t band
  originalComponentInputsCost q s+
    2*((haloInteriorCostBound p l s t u initialTarget 2 a b+
          realInteriorResidualOverhead p l s t u initialTarget 2 a b)+
      boundaryRhsPrepareCost V w N s+retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
      (haloInteriorCostBound p l s t u (recoveryTarget p bits) recoveryExp a b+
        recoveryToleranceGuardedOverhead p l s t u bits 2 a b)+
      sharedPageRetireResidualCost s w+retireCountedLineCost N w)+
    cleanComponentTransitionCost q s+cleanFinishComponentsCost q s+24*s*w+15*s+15+
    2000*(N+1)*(12*band+1)*(rmulCost w+w+1)

theorem sharedComplexBatchLineCost_geometry_le {s t b : ℕ} [NeZero s] (hst : s < t) (hbS : b ≤ s)
    (p u l a target : ℕ) :
    sharedComplexBatchLineCost p u l s t a b target ≤
      sharedComplexBatchGeometryLineCost p u l s t a b target := by
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  have hres := realInteriorResidualCost_geometry_le hst p l u (initialSchurTarget p u bits 2) 2 a b
  have hrec := recoveryToleranceCost_geometry_le hst p l u bits 2 a b
  have hguard := recoveryToleranceOverhead_guarded_le hst p l u bits 2 a b hbS
  apply (sharedComplexBatchLineCost_boundary_le p u l s t a b target).trans
  dsimp only [sharedComplexBatchNonBoundaryLineCost,sharedComplexBatchGeometryLineCost]
  dsimp only [bits,N] at hres hrec hguard
  omega

theorem sharedComplexClosedBatchCost_geometry_le {s t b : ℕ} [NeZero s] (hst : s < t) (hbS : b ≤ s)
    (p u l a target replicas : ℕ) :
    sharedComplexClosedBatchCost p u l s t a b target replicas ≤
      sharedComplexBatchKeyCost p u l s t a b target+
        replicas*sharedComplexBatchGeometryLineCost p u l s t a b target := by
  rw [sharedComplexClosedBatchCost_affine]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left replicas (sharedComplexBatchLineCost_geometry_le hst hbS p u l a target)) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
