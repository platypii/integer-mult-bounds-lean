module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPassesStock
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Residual archive and endpoint controls add only linear stream volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {Q A : ℕ} {P₀ U : Type}

theorem windowedSchurResidualWorkspace_le_volume
    (J ringPush batchPush rowPush p l s t u target rhsExp a b : ℕ) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    windowedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target rhsExp a b ≤
      interiorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target rhsExp) rhsExp a b+
      10000*(s+a+b+1)*(q+1) := by
  dsimp only
  unfold windowedSchurResidualWorkspace archivedSchurResidualWorkspace
    releasedSchurResidualWorkspace realInteriorResidualWorkspace initializedInteriorResidualWorkspace
    archiveResidualPrefixCost retireInitialInteriorCost realResidualProjectionCost initializeInteriorOutputCost
  ring_nf
  omega

theorem cyclicResidualPassesWorkspace_le_volume
    (J ringPush batchPush rowPush p l s t u target rhsExp a n : ℕ)
    (ha : a ≤ s) (hn : n ≤ s) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let target' := initialSchurTarget p u target rhsExp
    cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target rhsExp a n ≤
      interiorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target' rhsExp a (a+min n (s-a))+
      interiorResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target' rhsExp 0 (n-min n (s-a))+
      60000*(s+1)*(q+1) := by
  dsimp only
  have h₁ := windowedSchurResidualWorkspace_le_volume (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target rhsExp a (a+min n (s-a))
  have h₂ := windowedSchurResidualWorkspace_le_volume (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target rhsExp 0 (n-min n (s-a))
  have hscalar (x y : ℕ) (hx : x ≤ s) (hy : y ≤ s) :
      10000*(s+x+y+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) ≤
      30000*(s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) := by
    calc
      _ ≤ 10000*(s+s+s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) := by gcongr
      _ ≤ _ := by ring_nf; omega
  have hc₁ := hscalar a (a+min n (s-a)) ha (by omega)
  have hc₂ := hscalar 0 (n-min n (s-a)) (by omega) (by omega)
  unfold cyclicResidualPassesWorkspace
  dsimp only at h₁ h₂
  have hadd : 30000*(s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)+
      30000*(s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) =
      60000*(s+1)*(executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1) := by ring
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
