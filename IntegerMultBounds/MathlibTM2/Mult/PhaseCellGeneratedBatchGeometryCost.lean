module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedInteriorGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchCost

/-! A geometry ledger for the complete generated batch, with one construction bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def cachedRealComponentGeometryCost (p u l s t a b target V : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  cachedRealResidualGeometryCost p l s t u (initialSchurTarget p u bits 2) 2 a b+
    boundaryRhsPrepareCost V w N s+preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1)+
    retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
    cachedRecoveryGeometryCost p l s t u bits 2 a b+sharedPageRetireResidualCost s w+retireCountedLineCost N w

theorem placedCachedRealComponentCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p u l a b target V : ℕ) (hb : b ≤ s) :
    placedCachedRealComponentCost p u l s t a b target V ≤
      cachedRealComponentGeometryCost p u l s t a b target V := by
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  have hres := placedCachedRealInteriorResidualCost_geometry_le hst p l u
    (initialSchurTarget p u bits 2) 2 a b hb
  have hrec := placedCachedRecoveryToleranceCost_geometry_le hst p l u bits 2 a b hb
  dsimp only [placedCachedRealComponentCost,cachedRealComponentGeometryCost]
  dsimp only [bits,N] at hres hrec
  omega

noncomputable def generatedComplexGeometryLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  originalComponentInputsCost q s + 2*cachedRealComponentGeometryCost p u l s t a b (target+1) V +
    cleanComponentTransitionCost q s + cleanFinishComponentsCost q s + 24*s*w + 15*s + 15

theorem generatedComplexLineCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p u l a b target : ℕ) (hb : b ≤ s) :
    generatedComplexLineCost p u l s t a b target ≤
      generatedComplexGeometryLineCost p u l s t a b target := by
  have h := placedCachedRealComponentCost_geometry_le hst p u l a b (target+1)
    (publicationGeometryWidth t (PhaseCellBand.width p u)) hb
  dsimp only [generatedComplexLineCost,placedCachedBoundaryPairCost,generatedComplexGeometryLineCost]
  omega

theorem generatedClosedComplexBatchCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p u l a b target replicas : ℕ) (hb : b ≤ s) :
    generatedClosedComplexBatchCost p u l s t a b target replicas ≤
      generatedClosedComplexBatchCost p u l s t a b target 0 +
        replicas*generatedComplexGeometryLineCost p u l s t a b target := by
  rw [generatedClosedComplexBatchCost_eq]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left replicas (generatedComplexLineCost_geometry_le hst p u l a b target hb)) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
