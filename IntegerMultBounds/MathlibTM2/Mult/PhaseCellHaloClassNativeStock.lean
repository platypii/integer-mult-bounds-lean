module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedControlledHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Gathering, publication controls and scatter are native linear stream work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type}

theorem protectedPublicationControls_native :
    mnNativePushBound 8 (protectedPublicationControls (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [protectedPublicationControls,publicationControls,trimAdvanceLoopBody,trimAdvance,
    gatherRead,gatherReadStep,WordCmd.peekRp,discardPrefix,unaryProduct,transfer,transferAct,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem rawNaturalGather_native :
    mnNativePushBound 8 (rawNaturalGather (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [rawNaturalGather,generateRuntimeWidth,naturalGather,gatherOffset,gatherBatch,
    gatherLoopBody,gatherPacket,gatherNext,gatherRead,gatherReadStep,WordCmd.peekRp,
    unaryProduct,copyPrefix,copyR,copyStep,transfer,transferAct,clearWords,umul,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem protectedControlledHaloGroupInput_native :
    mnNativePushBound 8 (protectedControlledHaloGroupInput (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨protectedPublicationControls_native,embProg_native groupReg id _ ?_⟩
  exact ⟨rawNaturalGather_native,(by
    induction ([(111 : Fin 117),113] : List (Fin 117)) with
    | nil => exact Nat.zero_le _
    | cons r rs ih => exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩)⟩

theorem finishNaturalClass_native :
    mnNativePushBound 8 (finishNaturalClass (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [finishNaturalClass,retireGroupRHS,protectedScatter,scatterBatch,scatterLoopBody,
    scatterPacket,gatherRead,gatherReadStep,WordCmd.peekRp,discardPrefix,
    clearWords,unaryProduct,transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
