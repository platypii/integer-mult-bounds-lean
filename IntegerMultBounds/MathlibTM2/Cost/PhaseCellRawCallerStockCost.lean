module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedFamilyStockCost

/-! The raw caller pays headers, shared setup and a fixed number of step allowances. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyInverseCallerStockCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (A W p u l target : ℕ) :
    familyInverseCallerStockCost A W p u l target s t ≤
      (inverseScalarAtoms p s t u 0 s*tblC W 0+
        inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
        inverseReleaseCost W (inverseMasterValues p u l target s t 0 s))+
      generatedFamilyComplexSetupCostBound A p u l s t 0 s target+
      7*familyComplexBatchStepCost A p u l s t 0 s target := by
  let K := familyComplexBatchStepCost A p u l s t 0 s target
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hK : 8*(s*w)+8 ≤ K := by
    dsimp only [K,familyComplexBatchStepCost,w,bits]
    omega
  have hstock : generatedClosedFamilyComplexBatchStockCost A p u l s t 0 s target 1 ≤
      generatedFamilyComplexSetupCostBound A p u l s t 0 s target+K+36*s*w := by
    simpa only [mul_one] using generatedClosedFamilyComplexBatchStockCost_le hst A p u l 0 s target 1
  unfold familyInverseCallerStockCost
  nlinarith only [hstock,hK]

/-- The explicit raw allowance already pays one input line and the scalar word width. -/
theorem familyInverseCallerStockCost_input_le (A W p u l target s t : ℕ) [NeZero s] :
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    s*w+W ≤ familyInverseCallerStockCost A W p u l target s t := by
  dsimp only
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hatoms : 1 ≤ inverseScalarAtoms p s t u 0 s := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have htable : W ≤ tblC W 0 := by
    unfold tblC
    nlinarith only [Nat.zero_le (W*W)]
  have hmul : tblC W 0 ≤ inverseScalarAtoms p s t u 0 s*tblC W 0 := by
    nlinarith only [hatoms,Nat.zero_le (tblC W 0)]
  have hclosed : s*w ≤ generatedClosedFamilyComplexBatchStockCost A p u l s t 0 s target 1 := by
    dsimp only [generatedClosedFamilyComplexBatchStockCost,generatedFactorFamilyComplexBatchStockCost,
      generatedCouplingFamilyComplexBatchStockCost,generatedFamilyComplexBatchStockCost,
      familyComplexBatchStockCost,w,bits]
    simp only [Nat.one_mul]
    omega
  have hpref := htable.trans hmul
  change s*w+W ≤ _
  unfold familyInverseCallerStockCost
  omega

end IntegerMultBounds.MathlibTM2.Cost
