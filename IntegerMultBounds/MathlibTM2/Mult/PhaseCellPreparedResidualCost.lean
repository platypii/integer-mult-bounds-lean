module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryCost

/-! Normalization and unscaling preserve the repeated boundary row-bandwidth allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast

theorem preparedResidualSolveCost_le (q N W : ℕ) (hW : 1 ≤ W) :
    preparedResidualSolveCost q (2*q+8) N W ≤
      1000*(N+1)*W*(rmulCost (2*q+8)+(2*q+8)+1) := by
  have hbase := preparedBoundarySolveCost_le (2*q+8) N W hW
  have he : q/2-1 ≤ q := by omega
  have hh : q/2 ≤ q := Nat.div_le_self ..
  have hm := Nat.mul_le_mul_left (N+1) hW
  have hM := Nat.mul_le_mul_right (rmulCost (2*q+8)) hm
  have hq := Nat.mul_le_mul_right (2*q+8) hm
  dsimp [preparedResidualSolveCost,preparedBoundaryUnscaleCost,
    generatedBoundaryNormalizeCost,boundaryNormalizePhysicalCost,boundaryNormalizeCost,
    generatedBoundaryUnscaleCost,boundaryUnscalePhysicalCost,boundaryScalarInPlaceCost,
    preparedBoundarySolveCost] at *
  nlinarith only [hbase,he,hh,hW,hM,hq,Nat.zero_le (N*q),
    Nat.zero_le (N*rmulCost (2*q+8)),Nat.zero_le (W*rmulCost (2*q+8)),
    Nat.zero_le (N*W*rmulCost (2*q+8))]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
