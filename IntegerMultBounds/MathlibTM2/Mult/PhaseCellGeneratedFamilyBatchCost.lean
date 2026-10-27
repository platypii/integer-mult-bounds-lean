module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedClosedFamilyComplexBatch

/-! Separate actual one-time construction from the repeated complex solve and release work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The actual incremental cost of one additional complex input, including its release clocks. -/
noncomputable def generatedFamilyComplexLineCost (A p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  originalComponentInputsCost q s + familyBoundaryPairCost A p u l s t a b target V +
    24*s*w + 15*s + 15

/-- Construction, both cache lifecycles and fixed cleanup are paid only once. -/
theorem generatedClosedFamilyComplexBatchCost_eq (A p u l s t a b target replicas : ℕ) [NeZero s] :
    generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas =
      generatedClosedFamilyComplexBatchCost A p u l s t a b target 0 +
        replicas*generatedFamilyComplexLineCost A p u l s t a b target := by
  dsimp only [generatedClosedFamilyComplexBatchCost,generatedFamilyComplexLineCost,
    placedFactorBatchReleaseCostBound]
  ring

/-- The same generated key supports concatenated batches without another setup bill. -/
theorem generatedClosedFamilyComplexBatchCost_add (A p u l s t a b target m n : ℕ) [NeZero s] :
    generatedClosedFamilyComplexBatchCost A p u l s t a b target (m+n) =
      generatedClosedFamilyComplexBatchCost A p u l s t a b target m +
        n*generatedFamilyComplexLineCost A p u l s t a b target := by
  rw [generatedClosedFamilyComplexBatchCost_eq, generatedClosedFamilyComplexBatchCost_eq A p u l s t a b target m]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
