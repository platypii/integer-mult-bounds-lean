module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageClosedComplexBatch

/-! Exact one-key setup/release and repeated-line decomposition of the executed batch cost. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def sharedComplexBatchKeyCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  sharedComplexClosedBatchCost p u l s t a b target 0

noncomputable def sharedComplexBatchLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  originalComponentInputsCost q s+
    sharedPageBoundaryPairCost p u l s t a b target (publicationGeometryWidth t (PhaseCellBand.width p u))+
    24*s*w+15*s+15

theorem sharedComplexClosedBatchCost_affine (p u l s t a b target replicas : ℕ) [NeZero s] :
    sharedComplexClosedBatchCost p u l s t a b target replicas =
      sharedComplexBatchKeyCost p u l s t a b target+
        replicas*sharedComplexBatchLineCost p u l s t a b target := by
  dsimp only [sharedComplexClosedBatchCost,sharedComplexBatchKeyCost,sharedComplexBatchLineCost,
    sharedComplexBatchReleaseCostBound]
  ring

theorem sharedComplexClosedBatchCost_mono (p u l s t a b target : ℕ) [NeZero s]
    {replicas replicas' : ℕ} (h : replicas ≤ replicas') :
    sharedComplexClosedBatchCost p u l s t a b target replicas ≤
      sharedComplexClosedBatchCost p u l s t a b target replicas' := by
  rw [sharedComplexClosedBatchCost_affine,sharedComplexClosedBatchCost_affine]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- Groups concatenated under a single reuse key pay the key charge once. -/
theorem sharedComplexClosedBatchCost_groups (p u l s t a b target : ℕ) [NeZero s]
    (counts : List ℕ) :
    sharedComplexClosedBatchCost p u l s t a b target counts.sum =
      sharedComplexBatchKeyCost p u l s t a b target+
        (counts.map fun N => N*sharedComplexBatchLineCost p u l s t a b target).sum := by
  rw [sharedComplexClosedBatchCost_affine]
  congr 1
  induction counts with
  | nil => simp
  | cons N counts ih => simp only [List.sum_cons,List.map_cons,Nat.add_mul,ih]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
