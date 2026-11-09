module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireInitialInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveResidualPrefix
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Retiring and archiving owned residual prefixes use only linear native work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type}

theorem originalInputClock_native :
    mnNativePushBound 8 (originalInputClock (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  refine ⟨embProg_native componentReg id _ ?_,?_⟩
  · simp [couplingHeaderWidth,generateWordWidth,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · simp [unaryProduct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem retireInitialInterior_native :
    mnNativePushBound 8 (retireInitialInterior (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [retireInitialInterior,originalInputClock_native,discardPrefix,transfer,transferAct,clearWords,
    scanR,drainR,popDo,keepIn,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem archiveResidualPrefix_native :
    mnNativePushBound 8 (archiveResidualPrefix (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [archiveResidualPrefix,originalInputClock_native,movePrefix,transfer,transferAct,clearWords,
    scanR,drainR,popDo,keepIn,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
