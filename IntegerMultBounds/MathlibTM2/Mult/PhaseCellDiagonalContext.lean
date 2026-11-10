module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteDiagonalBatch

/-! Ordinary dimensions and blank work required by the existing diagonal
executor. The whole context is preserved by a recovery-bank frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
variable {A : ℕ}

structure DiagonalContext (s t u p w B a radius rows N : ℕ) (S : Stacks tapes A) : Prop where
  source : (S.R (recovery (.parameter 4))).length = s
  target : (S.R (recovery (.parameter 5))).length = t
  band : (S.R (recovery (.parameter 1))).length = u
  precision : (S.R (recovery (.parameter 0))).length = p
  precisionCopy : (S.R (recovery (.control .precision))).length = p
  packet : (S.R (recovery (.control .packet))).length = w
  width : (S.R diagonalWidthSource).length = B
  origin : (S.R diagonalHaloStart).length = a
  offset : (S.R diagonalCropOffset).length = radius
  rows : (S.R diagonalCropRows).length = rows
  replicas : (S.R (recovery (.control .replicas))).length = N
  fresh : DiagonalFresh S

theorem DiagonalContext.frame {s t u p w B a radius rows N : ℕ} {S F : Stacks tapes A}
    (h : DiagonalContext s t u p w B a radius rows N S)
    (hleft : F.L = S.L) (hframe : ∀ i, F.R (recovery i) = S.R (recovery i)) :
    DiagonalContext s t u p w B a radius rows N F := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hframe]; exact h.source
  · rw [hframe]; exact h.target
  · rw [hframe]; exact h.band
  · rw [hframe]; exact h.precision
  · rw [hframe]; exact h.precisionCopy
  · rw [hframe]; exact h.packet
  · change (F.R (recovery _)).length = _
    rw [hframe]; exact h.width
  · change (F.R (recovery _)).length = _
    rw [hframe]; exact h.origin
  · change (F.R (recovery _)).length = _
    rw [hframe]; exact h.offset
  · change (F.R (recovery _)).length = _
    rw [hframe]; exact h.rows
  · rw [hframe]; exact h.replicas
  · exact ⟨fun i => (congrFun hleft i).trans (h.fresh.left i),
      fun i => (hframe (.work i)).trans (h.fresh.work i)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
