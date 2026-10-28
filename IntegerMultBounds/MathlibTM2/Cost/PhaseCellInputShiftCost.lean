module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridFamilyInverseBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNormalizationCost

/-! Exact input conversion preserves the raw caller's time and stock envelopes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem inputShiftBatchCost_le_roundCost (W p u l target s t a b n : ℕ) [NeZero s] :
    inputShiftBatchCost W p u l target s t a b n ≤
      2*inverseRoundBatchCost W p u l target s t a b n := by
  unfold inputShiftBatchCost inverseRoundBatchCost
  have hs := Nat.mul_le_mul_right (tblC W 0)
    (show inverseScalarAtoms p s t u a b+22 ≤ 2*(inverseScalarAtoms p s t u a b+4*Nat.size (4*p)+52) by omega)
  let w := 8*inverseExecutionExponent p l target
    (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8
  have hc := Nat.mul_le_mul_left n (show 20*w+44 ≤ 2*(14*w+23) by omega)
  dsimp [w] at hc
  nlinarith only [hs,hc]

theorem inputShiftBatchCost_le_callerCost (A W p u l target s t a b N : ℕ) [NeZero s] :
    inputShiftBatchCost W p u l target s t a b (N*s) ≤
      16*familyInverseBatchCallerCost A W p u l s t a b target N := by
  have h := inputShiftBatchCost_le_roundCost W p u l target s t a b (N*s)
  have hr := inverseRoundBatchCost_le_callerCost A W p u l target s t a b N
  omega

theorem inputShiftBatchCost_le_callerStock (A W p u l target s t a b N : ℕ) [NeZero s] :
    inputShiftBatchCost W p u l target s t a b (N*s) ≤
      16*familyInverseBatchCallerStockCost A W p u l s t a b target N := by
  have h := inputShiftBatchCost_le_roundCost W p u l target s t a b (N*s)
  have hr := inverseRoundBatchCost_le_callerStock A W p u l target s t a b N
  omega

theorem gridFamilyInverseBatchCost_le_callerCost (A W p u l target s t a b N : ℕ) [NeZero s] :
    gridFamilyInverseBatchCost A W p u l s t a b target N ≤
      41*familyInverseBatchCallerCost A W p u l s t a b target N := by
  have h := inputShiftBatchCost_le_callerCost A W p u l target s t a b N
  have hr := inverseRoundBatchCost_le_callerCost A W p u l target s t a b N
  unfold gridFamilyInverseBatchCost normalizedFamilyInverseBatchCost
  omega

theorem gridFamilyInverseBatchStockCost_le_callerStock (A W p u l target s t a b N : ℕ) [NeZero s] :
    gridFamilyInverseBatchStockCost A W p u l s t a b target N ≤
      41*familyInverseBatchCallerStockCost A W p u l s t a b target N := by
  have h := inputShiftBatchCost_le_callerStock A W p u l target s t a b N
  have hr := inverseRoundBatchCost_le_callerStock A W p u l target s t a b N
  unfold gridFamilyInverseBatchStockCost normalizedFamilyInverseBatchStockCost
  omega

end IntegerMultBounds.MathlibTM2.Cost
