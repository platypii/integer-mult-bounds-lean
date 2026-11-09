module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicFactorPageStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualUniformBound
import Mathlib.Tactic.Ring

/-! Table publication adds linear volume to a single numerical column reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type}

theorem cyclicTableUniformWorkspace_le_volume
    (J ringPush batchPush rowPush cap p l s t u target a n : ℕ) [NeZero s] :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let V := publicationGeometryWidth t band
    cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush cap p l s t u target a n ≤
    originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u+
      cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target 2 a n+
      8*cap+100000*(B.card+s+band+1)*(V+q+1) := by
  dsimp only
  unfold cyclicTableUniformWorkspace cyclicCollectionUniformWorkspace
    scaledBandControls24CostBound retireCyclicColumnStreamsCost
  dsimp only
  ring_nf
  omega

theorem preparedCyclicFactorPageWorkspace_le_volume
    (J ringPush batchPush rowPush p l s t u target a n : ℕ) [NeZero s] :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    preparedCyclicFactorPageWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target a n ≤
      cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush (cyclicTableEntryCostBound p l s t u target a n)
        p l s t u target a n+
      15000000*(B.card+band+1)*(band+1)*(q+1) := by
  dsimp only
  have h := scaledGeneratedFactorPageWorkspace24_le
    (executionPrecision p l (initialSchurTarget p u target 2) 2)
    (PhaseCellBand.width p u)
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  unfold preparedCyclicFactorPageWorkspace preparedCyclicColumnsWorkspace
  dsimp only
  simp only [executionWidth,executionPrecision] at h ⊢
  ring_nf at h ⊢
  omega

theorem cyclicTableUniformWorkspace_le_components
    (J ringPush batchPush rowPush cap p l s t u target a n : ℕ) [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hn : n ≤ s) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let V := publicationGeometryWidth t band
    cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush cap p l s t u target a n ≤
      originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u+
      (2*interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u (initialSchurTarget p u target 2) 2+
        60000*(s+1)*(q+1))+
      8*cap+100000*(B.card+s+band+1)*(V+q+1) := by
  apply (cyclicTableUniformWorkspace_le_volume J ringPush batchPush rowPush cap p l s t u target a n).trans
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
    (cyclicResidualPassesWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target 2 a n hst ha hn) _) _) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
