module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPassGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedRealComponent
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost

/-! Price both executed interior solves and cached coupling passes by their physical geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def cachedRealResidualGeometryCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  haloInteriorCostBound p l s t u target rhsExp a b +
    initializeInteriorOutputCost q s +
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b +
    realResidualProjectionCost q s

theorem placedCachedRealInteriorResidualCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p l u target rhsExp a b : ℕ) (hb : b ≤ s) :
    placedCachedRealInteriorResidualCost p l s t u target rhsExp a b ≤
      cachedRealResidualGeometryCost p l s t u target rhsExp a b := by
  have hsolve := solveHaloInteriorCost_le hst p l u target rhsExp a b
  have hpass := placedCachedRestoredCouplingPassCost_geometry_le hst false
    (2^15*p) (executionPrecision p l target rhsExp) u (PhaseCellBand.width p u) a b hb
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    unfold executionWidth executionPrecision
    omega
  dsimp only [placedCachedRealInteriorResidualCost,placedCachedRestoredInteriorResidualCost,
    placedCachedInitializedInteriorResidualCost,placedCachedInteriorResidualCost,
    interiorForCouplingCost,cachedRealResidualGeometryCost]
  rw [hw]
  dsimp only [placedCachedRestoredCouplingPassCost] at hpass
  omega

noncomputable def cachedRecoveryGeometryCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let stageTarget := recoveryTarget p target
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p stageTarget rhsExp boundaryExp countExp) rhsExp
  let recoveryExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  retireAmbientSourceCost q s +
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b +
    initializeInteriorOutputCost (executionPrecision p l stageTarget recoveryExp) s +
    haloInteriorCostBound p l s t u stageTarget recoveryExp a b +
    publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

theorem placedCachedRecoveryToleranceCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p l u target rhsExp a b : ℕ) (hb : b ≤ s) :
    placedCachedRecoveryToleranceCost p l s t u target rhsExp a b ≤
      cachedRecoveryGeometryCost p l s t u target rhsExp a b := by
  have hsolve := solveHaloInteriorCost_le hst p l u (recoveryTarget p target)
    (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) a b
  have hpass := placedCachedRestoredCouplingPassCost_geometry_le hst true (2^15*p)
    (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp
      (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    u (PhaseCellBand.width p u) a b hb
  dsimp only [placedCachedRecoveryToleranceCost,placedCachedRecoveryPublishedHaloCost,
    placedCachedRecoveryInteriorCost,initializedInteriorCost,cachedRecoveryGeometryCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
