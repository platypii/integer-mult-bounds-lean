module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedMaskedSpatialRowStock

/-! Native restoration uses its linear traffic bill, with no numerical scratch charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type}

theorem restoreIntervalCouplingPass_native : mnNativePushBound 3
    (restoreIntervalCouplingPass (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [restoreIntervalCouplingPass,binaryRestoreCouplingCursors,binaryRestoreCouplingIndex,
    binaryRestoreCouplingRibbon,toUnary,hornerIter,udbl,eachSym,discardPrefix,
    transferCountedLine,unaryProduct,scanP,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    transfer,transferAct,uclear,moveR,moveStep,whileR,peekR,popPush,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
