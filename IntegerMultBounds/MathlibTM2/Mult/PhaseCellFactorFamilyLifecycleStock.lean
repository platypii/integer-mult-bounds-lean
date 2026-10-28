module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyFactorBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchReleaseCost

/-! The factor-page lifecycle adds its bounded construction and release to the
already certified generated family batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def generatedFactorFamilyComplexBatchStockCost
    (A p u l s t a b target replicas : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 N
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  (constructedBoundaryFactorCost p u l s t a b solveTarget 2+
    sharedPagePublicationSetupCost N V w s)+
    generatedCouplingFamilyComplexBatchStockCost A p u l s t a b target V replicas

noncomputable def generatedClosedFamilyComplexBatchStockCost
    (A p u l s t a b target replicas : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  let W := 12*band+1
  generatedFactorFamilyComplexBatchStockCost A p u l s t a b target replicas+
    placedFactorBatchReleaseCostBound s replicas N W w V
      (boundaryPermanentSizeBound q band N) (12*band*w+N*W)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
