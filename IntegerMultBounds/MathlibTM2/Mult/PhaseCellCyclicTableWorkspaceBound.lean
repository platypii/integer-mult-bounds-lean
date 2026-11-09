module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableEntryCostBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCollectionWorkspaceBound
import Mathlib.Tactic.GCongr

/-! One coordinate-independent workspace reserve for the complete cyclic table column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type}

@[irreducible] def cyclicTableUniformWorkspace
    (J ringPush batchPush rowPush cap p l s t u target a n : ℕ) [NeZero s] : ℕ :=
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let V := publicationGeometryWidth t band
  2*(4*B.card+4)+
    (3*(B.card*(12*V+11)+27*V+6*s+36)+
      (originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u+
        cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target 2 a n))+
    (2*(4*B.card+4)+(cyclicCollectionUniformWorkspace cap q band B.card+
      8*retireCyclicColumnStreamsCost q s))

theorem cyclicTableColumnWorkspace_le_uniform
    (J ringPush batchPush rowPush cap p l s t u target a n k : ℕ) [NeZero s]
    (hk : k ≤ (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) :
    cyclicTableColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush cap p l s t u target a n k ≤
    cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush cap p l s t u target a n := by
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let j := bFoldAt s B k
  have hj : j.val < s := j.val_lt
  have ho := arbitraryOriginalColumnWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
    rowPush p q s t u j.val hj
  have hc := preparedCyclicBandCollectionWorkspace_le_uniform cap q band B.card k hk
  unfold cyclicTableColumnWorkspace retainedIndexedCyclicColumnWorkspace indexedCyclicColumnWorkspace
    generatedCyclicColumnWorkspace cyclicTableUniformWorkspace
  dsimp only
  change arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    rowPush p (executionPrecision p l (initialSchurTarget p u target 2) 2) s t u
      (bFoldAt s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) k).val ≤ _ at ho
  dsimp only [q,band,B] at hc
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
