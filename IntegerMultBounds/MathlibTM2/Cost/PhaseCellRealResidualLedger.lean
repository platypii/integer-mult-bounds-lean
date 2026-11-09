module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealInteriorResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPasses
import Mathlib.Tactic.Ring

/-! Expose the two numerical calls inside a real residual pass. All other
work is scalar-header lifecycle and linear stream volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN

/-- Uniform lifecycle overhead for bounded physical endpoints. This is the
scalar envelope used when the working precision comes from a joint boundary. -/
theorem residualLifecycleCost_poly (p q s t u band a b cw : ℕ)
    (ht : 1 ≤ t) (hp : p ≤ t) (hq : q ≤ cw*t) (hs : s ≤ t)
    (hu : u ≤ t) (hband : band ≤ t) (ha : a ≤ t) (hb : b ≤ t) :
    10000*(2^15*p+q+s+t+u+band+a+b+1)*(q+1) ≤
      10000*(32775+cw)*(cw+1)*t^2 := by
  have hP := Nat.mul_le_mul_left 32768 hp
  have hsum : 2^15*p+q+s+t+u+band+a+b+1 ≤ (32775+cw)*t := by
    norm_num only [Nat.reducePow]
    nlinarith only [hP,hq,hs,hu,hband,ha,hb,ht]
  have hwidth : q+1 ≤ (cw+1)*t := by
    nlinarith only [hq,ht]
  have hprod := Nat.mul_le_mul hsum hwidth
  nlinarith only [hprod]

theorem realInteriorResidualCost_split (p l s t u target rhsExp a b : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    realInteriorResidualCost p l s t u target rhsExp a b =
      solveHaloInteriorCost p l s t u target rhsExp a b+
      borrowedCouplingPassCost false (2^15*p) q w s t u (PhaseCellBand.width p u) a b+
      installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      releaseCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
      46*s*w+27*s+24*q+102 := by
  dsimp only
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  unfold realInteriorResidualCost restoredInteriorResidualCost initializedInteriorResidualCost
    interiorResidualCost interiorForCouplingCost feedCouplingPassCost
    initializeInteriorOutputCost realResidualProjectionCost
  rw [hw]
  ring

/-- A complete windowed table pass reduces to the two existing numerical
prices and one polynomial scalar/stream allowance. -/
theorem windowedSchurResidualCost_le_numerical (p l s t u target rhsExp a b : ℕ) :
    let stage := initialSchurTarget p u target rhsExp
    let q := executionPrecision p l stage rhsExp
    let w := executionWidth p l stage rhsExp
    let band := PhaseCellBand.width p u
    windowedSchurResidualCost p l s t u target rhsExp a b ≤
      solveHaloInteriorCost p l s t u stage rhsExp a b+
      borrowedCouplingPassCost false (2^15*p) q w s t u band a b+
      10000*(2^15*p+q+s+t+u+band+a+b+1)*(q+1) := by
  dsimp only
  unfold windowedSchurResidualCost releasedSchurResidualCost
    archiveResidualPrefixCost retireInitialInteriorCost
  rw [realInteriorResidualCost_split]
  unfold installCouplingHeadersCost releaseCouplingHeadersCost
    executionPrecision executionWidth
  ring_nf
  omega

end IntegerMultBounds.MathlibTM2.Cost
