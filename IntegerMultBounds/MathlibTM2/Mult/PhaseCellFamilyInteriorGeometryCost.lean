module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPassGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyRealComponent
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloInteriorGeometryCost

/-! Price both executed interior solves and cached coupling passes by their physical geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyRealResidualGeometryCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  familyHaloInteriorGeometryCost p l s t u target rhsExp a b +
    initializeInteriorOutputCost q s +
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b +
    realResidualProjectionCost q s

theorem familyRealInteriorResidualCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p l u target rhsExp a b : ℕ) (hb : b ≤ s) :
    familyRealInteriorResidualCost A p l s t u target rhsExp a b ≤
      familyRealResidualGeometryCost p l s t u target rhsExp a b := by
  have hsolve := familySolveHaloInteriorCost_geometry_le hst A p l u target rhsExp a b
  have hpass := placedCachedRestoredCouplingPassCost_geometry_le hst false
    (2^15*p) (executionPrecision p l target rhsExp) u (PhaseCellBand.width p u) a b hb
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    unfold executionWidth executionPrecision
    omega
  dsimp only [familyRealInteriorResidualCost,familyRestoredInteriorResidualCost,
    familyInitializedInteriorCost,familyInteriorResidualCost,familyRealResidualGeometryCost]
  rw [hw]
  dsimp only [placedCachedRestoredCouplingPassCost] at hpass
  omega

noncomputable def familyRecoveryGeometryCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let stageTarget := recoveryTarget p target
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p stageTarget rhsExp boundaryExp countExp) rhsExp
  let recoveryExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  retireAmbientSourceCost q s +
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b +
    initializeInteriorOutputCost (executionPrecision p l stageTarget recoveryExp) s +
    familyHaloInteriorGeometryCost p l s t u stageTarget recoveryExp a b +
    publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

theorem familyRecoveryToleranceCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p l u target rhsExp a b : ℕ) (hb : b ≤ s) :
    familyRecoveryToleranceCost A p l s t u target rhsExp a b ≤
      familyRecoveryGeometryCost p l s t u target rhsExp a b := by
  have hsolve := familySolveHaloInteriorCost_geometry_le hst A p l u (recoveryTarget p target)
    (recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) a b
  have hpass := placedCachedRestoredCouplingPassCost_geometry_le hst true (2^15*p)
    (executionPrecision p l (recoveryFirstTarget p (recoveryTarget p target) rhsExp
      (stableInteriorExponent p rhsExp) (couplingCountExponent p u)) rhsExp)
    u (PhaseCellBand.width p u) a b hb
  dsimp only [familyRecoveryToleranceCost,familyRecoveryPublishedHaloCost,
    familyRecoveryInteriorCost,familyInitializedInteriorCost,familyRecoveryGeometryCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
