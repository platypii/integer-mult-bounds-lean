module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.StackResources

/-! The restoring gather uses only bounded native stack actions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem naturalGather_native (dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T) :
    mnNativePushBound 2 (naturalGather (P := P) (Q := Q) (A := A) (U := U)
      dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR) := by
  simp [naturalGather,gatherOffset,gatherBatch,gatherLoopBody,gatherPacket,gatherNext,gatherRead,
    gatherReadStep,WordCmd.peekRp,copyPrefix,copyR,copyStep,transfer,transferAct,unaryProduct,
    ucopy,umulSym,scanP,popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
