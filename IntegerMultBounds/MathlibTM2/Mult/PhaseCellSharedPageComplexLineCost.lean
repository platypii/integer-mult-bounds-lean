module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualCost

/-! Expose the two repeated boundary solves in each complete complex line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def sharedComplexBatchNonBoundaryLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  originalComponentInputsCost q s+
    2*(realInteriorResidualCost p l s t u (initialSchurTarget p u bits 2) 2 a b+
      boundaryRhsPrepareCost V w N s+retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
      recoveryToleranceCost p l s t u bits 2 a b+sharedPageRetireResidualCost s w+retireCountedLineCost N w)+
    cleanComponentTransitionCost q s+cleanFinishComponentsCost q s+24*s*w+15*s+15

theorem sharedComplexBatchLineCost_boundary (p u l s t a b target : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    sharedComplexBatchLineCost p u l s t a b target =
      sharedComplexBatchNonBoundaryLineCost p u l s t a b target+
        2*preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1) := by
  dsimp only [sharedComplexBatchLineCost,sharedComplexBatchNonBoundaryLineCost,
    sharedPageBoundaryPairCost,sharedPageRealComponentCost]
  ring

theorem sharedComplexBatchLineCost_boundary_le (p u l s t a b target : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    sharedComplexBatchLineCost p u l s t a b target ≤
      sharedComplexBatchNonBoundaryLineCost p u l s t a b target+
        2000*(N+1)*(12*PhaseCellBand.width p u+1)*(rmulCost w+w+1) := by
  dsimp only
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hsolve : preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1) ≤
      1000*(N+1)*(12*PhaseCellBand.width p u+1)*(rmulCost w+w+1) := by
    rw [hw]
    exact preparedResidualSolveCost_le q N (12*PhaseCellBand.width p u+1) (by omega)
  rw [sharedComplexBatchLineCost_boundary]
  exact Nat.add_le_add_left (by nlinarith only [hsolve]) _

theorem sharedComplexClosedBatchCost_boundary_le (p u l s t a b target replicas : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    sharedComplexClosedBatchCost p u l s t a b target replicas ≤
      sharedComplexBatchKeyCost p u l s t a b target+
        replicas*(sharedComplexBatchNonBoundaryLineCost p u l s t a b target+
          2000*(N+1)*(12*PhaseCellBand.width p u+1)*(rmulCost w+w+1)) := by
  dsimp only
  rw [sharedComplexClosedBatchCost_affine]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left replicas (sharedComplexBatchLineCost_boundary_le p u l s t a b target)) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
