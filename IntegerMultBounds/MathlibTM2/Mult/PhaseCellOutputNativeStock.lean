module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightNativeStock

/-! Output scale, generated shift controls and borrowed-page fetching are
native traffic, separate from the shared numerical weighting reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem scaleOutputPrefix_native :
    mnNativePushBound 3 (scaleOutputPrefix (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [scaleOutputPrefix,branchWords,halfCount,halfPairAct,takeFromWords,takePrefix,unaryProduct,
    Host.shiftInto,Host.shiftWords,Host.Shift.shiftWord,Host.Shift.counted,Host.Shift.zeroStep,Host.Shift.copyStep,
    Host.Shift.dropStep,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,
    popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem outputHeaders_native :
    mnNativePushBound 3 (outputHeaders (P := P) (T := 117) (Q := Q) (A := A) (U := U) 100 101 94 116 115 26 27) := by
  simp [outputHeaders,outputShiftHeader,extendOutputShift,quarterCount,halfCount,halfPairAct,
    complementHeader,releasePrefix,copyR,copyStep,transfer,transferAct,scanR,drainR,popDo,
    keepIn,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem fetchOutputTable_native :
    mnNativePushBound 3 (fetchOutputTable (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [fetchOutputTable,fetchPage,pageAddress,copyRepeated,branchWords,halfCount,halfPairAct,
    unaryProduct,copyAfterPrefix,copyPrefix,copyR,copyStep,transfer,transferAct,clearWords,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
