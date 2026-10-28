module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyCouplingKeyControls

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchStock

/-! One-time generated-family work surrounds the live repeated-batch stock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def generatedFamilyComplexBatchStockCost
    (A p u l s t a b target V replicas : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t band a b).card
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  prepareHaloWeightFamilyCost A (2^15*p) (executionStagePrecision p l stage 2+1)
    q l s t u band a b+
    familyComplexBatchStockCost s w replicas
      (originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8))+
    (2*(weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b
      (haloLengthKeys s t band a b))).length+2)

noncomputable def generatedCouplingFamilyComplexBatchStockCost
    (A p u l s t a b target V replicas : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t band a b).card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  couplingKeySetupCost (2^15*p) q s t u band a b+
    generatedFamilyComplexBatchStockCost A p u l s t a b target V replicas+
    couplingKeyReleaseCost (2^15*p) q s t u band a b
      (couplingCoefficientPage (2^15*p) q s t u band a b s).length

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
