module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyBatchGeometryCost

/-! The full resource ledger pays shared setup once, one body scratch bill,
and only linear input/output stock for additional replicas. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem generatedClosedFamilyComplexBatchStockCost_eq
    (A p u l s t a b target replicas : ℕ) [NeZero s] :
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas+2 =
      generatedClosedFamilyComplexBatchCost A p u l s t a b target 0+
        familyComplexBatchStepCost A p u l s t a b target+
        replicas*(17*s*w+15*s+4) := by
  dsimp only [generatedClosedFamilyComplexBatchStockCost,generatedFactorFamilyComplexBatchStockCost,
    generatedCouplingFamilyComplexBatchStockCost,generatedFamilyComplexBatchStockCost,
    familyComplexBatchStockCost,familyComplexBatchStepCost,generatedClosedFamilyComplexBatchCost,
    placedFactorBatchReleaseCostBound]
  ring

theorem generatedClosedFamilyComplexBatchStockCost_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target replicas : ℕ) :
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas ≤
      generatedFamilyComplexSetupCostBound A p u l s t a b target+
        familyComplexBatchStepCost A p u l s t a b target+36*replicas*s*w := by
  dsimp only
  let w := executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2
  have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hw : 1 ≤ w := by dsimp only [w,executionWidth]; omega
  have hsw : s ≤ s*w := Nat.le_mul_of_pos_right s hw
  have hswpos : 1 ≤ s*w := Nat.mul_pos hs hw
  have hcoef : 17*s*w+15*s+4 ≤ 36*s*w := by nlinarith only [hsw,hswpos]
  have hrep := Nat.mul_le_mul_left replicas hcoef
  have he : generatedClosedFamilyComplexBatchStockCost A p u l s t a b target replicas+2 =
      generatedClosedFamilyComplexBatchCost A p u l s t a b target 0+
        familyComplexBatchStepCost A p u l s t a b target+replicas*(17*s*w+15*s+4) :=
    generatedClosedFamilyComplexBatchStockCost_eq A p u l s t a b target replicas
  have hsetup := generatedClosedFamilyComplexBatchCost_setup_le hst A p u l a b target
  calc
    _ ≤ generatedFamilyComplexSetupCostBound A p u l s t a b target+
        familyComplexBatchStepCost A p u l s t a b target+replicas*(36*s*w) := by omega
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
