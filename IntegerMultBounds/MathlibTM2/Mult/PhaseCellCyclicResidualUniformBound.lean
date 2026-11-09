module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInteriorWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualVolumeBound
import Mathlib.Tactic.GCongr

/-! Both cyclic residual pieces use the same derived numerical allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type}

@[irreducible] def solveHaloInteriorUniformWorkspace (J R K p l s t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q (2*q+8) t u
  18*(200*tblC V V+10000*(P+N+q+l+s+t+u+band+s+s+1)*(V+q+1))+
    (haloKeySharedSetup J R K p l s t u target rhsExp ((s/(t-s)+1)-2*band)+
      haloKeyAuxWorkspace R K p l s t u target rhsExp V)

theorem solveHaloInteriorWorkspace_le_uniform
    (J R K p l s t u target rhsExp a b : ℕ)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) :
    solveHaloInteriorWorkspace J R K p l s t u target rhsExp a b ≤
      solveHaloInteriorUniformWorkspace J R K p l s t u target rhsExp := by
  apply (solveHaloInteriorWorkspace_le_components J R K p l s t u target rhsExp a b hst ha hb).trans
  unfold solveHaloInteriorUniformWorkspace
  dsimp only
  gcongr

@[irreducible] def interiorResidualUniformWorkspace
    (J ringPush batchPush rowPush p l s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  solveHaloInteriorUniformWorkspace J ringPush batchPush p l s t u target rhsExp+
    feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      false rowPush (2^15*p) q w s t u band+
    2000000*(p+q+s+t+u+band+1)

theorem interiorResidualWorkspace_le_uniform
    (J ringPush batchPush rowPush p l s t u target rhsExp a b : ℕ)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) :
    interiorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target rhsExp a b ≤
      interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target rhsExp := by
  apply (interiorResidualWorkspace_le_components J ringPush batchPush rowPush p l s t u target rhsExp a b ha hb).trans
  unfold interiorResidualUniformWorkspace
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (solveHaloInteriorWorkspace_le_uniform J ringPush batchPush p l s t u target rhsExp a b hst ha hb) _) _

theorem cyclicResidualPassesWorkspace_le_uniform
    (J ringPush batchPush rowPush p l s t u target rhsExp a n : ℕ)
    (hst : s < t) (ha : a ≤ s) (hn : n ≤ s) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target rhsExp a n ≤
      2*interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target rhsExp) rhsExp+
      60000*(s+1)*(q+1) := by
  apply (cyclicResidualPassesWorkspace_le_volume J ringPush batchPush rowPush
    p l s t u target rhsExp a n ha hn).trans
  have h₁ := interiorResidualWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target rhsExp) rhsExp
    a (a+min n (s-a)) hst ha (by omega)
  have h₂ := interiorResidualWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target rhsExp) rhsExp
    0 (n-min n (s-a)) hst (by omega) (by omega)
  simpa only [two_mul] using Nat.add_le_add_right (Nat.add_le_add h₁ h₂)
    (60000*(s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
