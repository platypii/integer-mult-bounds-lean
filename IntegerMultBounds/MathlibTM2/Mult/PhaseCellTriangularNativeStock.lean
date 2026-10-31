module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperBatch
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Row reversal and compaction use only native linear traffic. Their push bounds
are structural in the programs, independent of row and replica counts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem reverseInput_native :
    mnNativePushBound 3 (reverseInput (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [reverseInput,reverseRowsFromDimensions,reverseRowsInPlace,reverseRows,
    reverseRowLoopBody,reverseRowNext,reverseWords,reverseLoopBody,reverseNext,
    copyPrefix,copyR,copyStep,transfer,transferAct,unaryProduct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

theorem upperToLowerInput_native :
    mnNativePushBound 3 (upperToLowerInput (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [upperToLowerInput,upperCropFromDimensions,correlationBatch,correlationLoopBody,
    correlationNext,reverseSlice,reverseWords,reverseLoopBody,reverseNext,padding,upow2,udbl,usub,copyPrefix,copyR,copyStep,transfer,transferAct,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,dropTop,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
