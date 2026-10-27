module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageGeometryBatch

/-! Carry the executed geometry ledger through raw inverse scalar setup and release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem sharedPageClosedComplexCost_le_batch (p u l s t a b target : ℕ) [NeZero s] :
    sharedPageClosedComplexCost p u l s t a b target ≤
      sharedComplexClosedBatchCost p u l s t a b target 1 := by
  dsimp only [sharedPageClosedComplexCost,sharedComplexClosedBatchCost,
    sharedPageReleaseCostBound,sharedComplexBatchReleaseCostBound]
  simp only [one_mul,mul_one]
  ring_nf
  omega

noncomputable def sharedInverseCallerGeometryCost (W p u l target s t : ℕ) [NeZero s] : ℕ :=
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    (sharedComplexBatchKeyCost p u l s t 0 s target+
      sharedComplexBatchGeometryLineCost p u l s t 0 s target)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem sharedInverseCallerCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (W p u l target : ℕ) :
    sharedInverseCallerCost W p u l target s t ≤
      sharedInverseCallerGeometryCost W p u l target s t := by
  have hsingle := sharedPageClosedComplexCost_le_batch p u l s t 0 s target
  have hbatch := sharedComplexClosedBatchCost_geometry_le hst le_rfl p u l 0 target 1
  dsimp only [sharedInverseCallerCost,sharedInverseCallerGeometryCost]
  simp only [one_mul] at hbatch
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
