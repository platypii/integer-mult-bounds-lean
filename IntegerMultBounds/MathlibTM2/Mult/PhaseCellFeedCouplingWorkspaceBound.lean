module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorResidualStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnWorkspaceBound
import Mathlib.Tactic.Ring

/-! One coordinate-independent allowance covers either kind of coupling pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN
variable {Q A : ℕ} {P₀ U : Type}

@[irreducible] def feedCouplingUniformWorkspace (boundary : Bool)
    (rowPush P q w s t u band : ℕ) : ℕ :=
  spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary*
    couplingSourceSetupBound s t band w+
  (couplingGuardPush (Q := Q) (A := A) (U := U)*couplingGuardSetupBound s t band+
    (retainedCouplingPacketPush (Q := Q) (A := A) (U := U)*
      buildMarkedRowCoefficientPacketCost P q w s t u band 0+
      runPreparedPacketCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        rowPush P q w s t u band))+
  3*retireSpatialCouplingSourceCost s band w+500*(s+1)*(w+1)

theorem feedCouplingPassWorkspace_le_uniform (boundary : Bool)
    (rowPush P q w s t u band a b : ℕ) (ha : a ≤ s) (hb : b ≤ s) :
    feedCouplingPassWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      boundary rowPush P q w s t u band a b ≤
    feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      boundary rowPush P q w s t u band := by
  have hs := prepareSpatialCouplingSourceCost_le_uniform s t band a b w ha hb
  have hg := prepareCouplingGuardCost_le_uniform s t band a b ha hb
  have hs' := Nat.mul_le_mul_left
    (spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary) hs
  have hg' := Nat.mul_le_mul_left (couplingGuardPush (Q := Q) (A := A) (U := U)) hg
  unfold feedCouplingPassWorkspace borrowedCouplingPassWorkspace spatialCouplingRowsWorkspace
    runSpatialCouplingRowsWorkspace feedCouplingUniformWorkspace
  have hvolume : 3*(26*s*w+9*s+26)+2*(3*(12*s*w+9*s+12)) ≤ 500*(s+1)*(w+1) := by
    ring_nf
    omega
  omega

theorem interiorResidualWorkspace_le_components
    (J ringPush batchPush rowPush p l s t u target rhsExp a b : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    interiorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target rhsExp a b ≤
    solveHaloInteriorWorkspace J ringPush batchPush p l s t u target rhsExp a b+
      feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        false rowPush (2^15*p) q w s t u band+
      2000000*(p+q+s+t+u+band+1) := by
  dsimp only
  have hf := feedCouplingPassWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
    false rowPush (2^15*p) (executionPrecision p l target rhsExp)
    (executionWidth p l target rhsExp) s t u (PhaseCellBand.width p u) a b ha hb
  have hh : 8*installCouplingHeadersCost (2^15*p) (executionPrecision p l target rhsExp)
      s t u (PhaseCellBand.width p u) a b ≤
      2000000*(p+executionPrecision p l target rhsExp+s+t+u+PhaseCellBand.width p u+1) := by
    unfold installCouplingHeadersCost
    omega
  unfold interiorResidualWorkspace interiorForCouplingWorkspace
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
