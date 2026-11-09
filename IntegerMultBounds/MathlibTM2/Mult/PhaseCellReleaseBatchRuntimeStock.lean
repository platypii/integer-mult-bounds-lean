module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBatchRuntime
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Batch runtime retirement uses only linear native page and header traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type}

theorem releaseBatchRuntime_native :
    mnNativePushBound 8 (releaseBatchRuntime (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [releaseBatchRuntime,branchWords,halfCount,halfPairAct,releaseRuntimePages,
    swapCellPayload,swapAfterPrefix,releaseGeneratorPage,releaseWeightPage,releaseFromDimensions,
    releasePrefix,unaryProduct,umul,uadd,transfer,transferAct,clearWords,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
