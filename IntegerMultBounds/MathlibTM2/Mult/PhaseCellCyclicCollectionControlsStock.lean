module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledBandControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicColumnStreams
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Fixed native certificates for collection setup and owned-stream retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem scaledBandControls24_native :
    mnNativePushBound 25 (scaledBandControls (P := P) (Q := Q) (A := A) (U := U) 24) := by
  simp [scaledBandControls,scaledBandWidth,clippedBandControls,bandIntervalEndpoints,
    clipUnary,umul,ucopy,umulSym,usub,scanR,drainR,popDo,keepIn,pushN,
    popPush,dropTop,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem retireCyclicColumnStreams_native :
    mnNativePushBound 8 (retireCyclicColumnStreams (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [retireCyclicColumnStreams,residentColumnWidth,generateWordWidth,unaryProduct,
    discardPrefix,transfer,transferAct,clearWords,ucopy,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,popPush,uclear,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
