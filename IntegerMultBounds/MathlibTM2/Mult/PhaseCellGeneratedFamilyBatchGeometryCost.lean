module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInteriorGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyBatchCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchGeometryCost

/-! A geometry ledger for the complete generated batch, with one construction bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyRealComponentGeometryCost (p u l s t a b target V : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  familyRealResidualGeometryCost p l s t u (initialSchurTarget p u bits 2) 2 a b+
    boundaryRhsPrepareCost V w N s+preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1)+
    retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
    familyRecoveryGeometryCost p l s t u bits 2 a b+sharedPageRetireResidualCost s w+retireCountedLineCost N w

theorem familyRealComponentCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target V : ℕ) (hb : b ≤ s) :
    familyRealComponentCost A p u l s t a b target V ≤
      familyRealComponentGeometryCost p u l s t a b target V := by
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  have hres := familyRealInteriorResidualCost_geometry_le hst A p l u
    (initialSchurTarget p u bits 2) 2 a b hb
  have hrec := familyRecoveryToleranceCost_geometry_le hst A p l u bits 2 a b hb
  dsimp only [familyRealComponentCost,familyRealComponentGeometryCost]
  dsimp only [bits,N] at hres hrec
  omega

noncomputable def generatedFamilyComplexGeometryLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  originalComponentInputsCost q s + 2*familyRealComponentGeometryCost p u l s t a b (target+1) V +
    cleanComponentTransitionCost q s + cleanFinishComponentsCost q s + 24*s*w + 15*s + 15

theorem generatedFamilyComplexLineCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target : ℕ) (hb : b ≤ s) :
    generatedFamilyComplexLineCost A p u l s t a b target ≤
      generatedFamilyComplexGeometryLineCost p u l s t a b target := by
  have h := familyRealComponentCost_geometry_le hst A p u l a b (target+1)
    (publicationGeometryWidth t (PhaseCellBand.width p u)) hb
  dsimp only [generatedFamilyComplexLineCost,familyBoundaryPairCost,generatedFamilyComplexGeometryLineCost]
  omega

theorem generatedClosedFamilyComplexBatchCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target replicas : ℕ) (hb : b ≤ s) :
    generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas ≤
      generatedClosedFamilyComplexBatchCost A p u l s t a b target 0 +
        replicas*generatedFamilyComplexGeometryLineCost p u l s t a b target := by
  rw [generatedClosedFamilyComplexBatchCost_eq]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left replicas (generatedFamilyComplexLineCost_geometry_le hst A p u l a b target hb)) _

noncomputable def generatedFamilyComplexSetupCostBound (A p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  generatedComplexSetupCostBound p u l s t a b target+
    prepareHaloWeightFamilyCost A (2^15*p) (executionStagePrecision p l stage 2+1)
      q l s t u (PhaseCellBand.width p u) a b+8*s*w+14

/-- The new lifecycle adds exactly one numerical family construction and erasure. -/
theorem generatedClosedFamilyComplexBatchCost_setup_eq (A p u l s t a b target : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let stage := initialSchurTarget p u bits 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    generatedClosedFamilyComplexBatchCost A p u l s t a b target 0 =
      generatedClosedComplexBatchCost p u l s t a b target 0+
        prepareHaloWeightFamilyCost A (2^15*p) (executionStagePrecision p l stage 2+1)
          q l s t u (PhaseCellBand.width p u) a b+
        2*(weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u (PhaseCellBand.width p u) a b
          (haloLengthKeys s t (PhaseCellBand.width p u) a b))).length+2 := by
  dsimp only [generatedClosedFamilyComplexBatchCost,generatedClosedComplexBatchCost]
  ring

theorem generatedClosedFamilyComplexBatchCost_setup_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target : ℕ) :
    generatedClosedFamilyComplexBatchCost A p u l s t a b target 0 ≤
      generatedFamilyComplexSetupCostBound A p u l s t a b target := by
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  have hbase := generatedClosedComplexBatchCost_setup_le p u l s t a b target
  have hfamily := haloWeightKeyFamily_length_le hst A w q (2^15*p) u (PhaseCellBand.width p u) a b
  have hkeys := haloLengthKeys_length_le s t (PhaseCellBand.width p u) a b
  rw [generatedClosedFamilyComplexBatchCost_setup_eq]
  dsimp only [generatedFamilyComplexSetupCostBound]
  dsimp only [w,q,stage,bits,N] at hfamily
  nlinarith only [hbase,hfamily,hkeys]

theorem generatedClosedFamilyComplexBatchCost_full_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p u l a b target replicas : ℕ) (hb : b ≤ s) :
    generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas ≤
      generatedFamilyComplexSetupCostBound A p u l s t a b target+
        replicas*generatedFamilyComplexGeometryLineCost p u l s t a b target := by
  exact (generatedClosedFamilyComplexBatchCost_geometry_le hst A p u l a b target replicas hb).trans
    (Nat.add_le_add_right (generatedClosedFamilyComplexBatchCost_setup_le hst A p u l a b target) _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
