module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolveStock

/-! Shared numerical push bounds travel with the retained boundary solver. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main

structure BoundarySolvePushBounds {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q) where
  normalize : ℕ
  unscale : ℕ
  reciprocal : ℕ
  column : ℕ
  normalize_push : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya) (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya))) ≤ normalize
  unscale_push : mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya) (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya))) ≤ unscale
  reciprocal_push : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .hv .xa .hc)) ≤ reciprocal
  column_push : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .ya .xs .pr)) ≤ column

def BoundarySolvePushBounds.workspace {Q A : ℕ} {U : Type} {hQ : SS.states ≤ Q}
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (q w N W : ℕ) : ℕ :=
  preparedResidualSolveWorkspace push.normalize push.unscale push.reciprocal push.column q w N W

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
