module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicColumnEntryStep

/-! Cyclic entry selection is native: scalar addressing and restored word copies
use a fixed push bound independent of the selected row and collection length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
variable {Q A : ℕ} {P U : Type}

theorem cyclicColumnEntryStep_native :
    mnNativePushBound 8 (cyclicColumnEntryStep (P := P) (Q := Q) (A := A) (U := U)) := by
  have hscalar : mnNativePushBound 8
      (unaryScalarResult (P := P) (Q := Q) (A := A) (U := U)
        cyclicEntryReg 20 21 22 23 24 (cyclicResidualIndexInputs 121 144 145 139)
        cyclicResidualIndexCode 4 25) :=
    mnNativePushBound_mono (by decide) (unaryScalarResult_native ..)
  simp [cyclicColumnEntryStep,selectedCyclicColumnEntry,selectResidentCoordinate,
    residentColumnWidth,generatedCyclicResidualEntry,cyclicResidualIndexFromUnary,
    hscalar,generateWordWidth,loadResidentCoordinate,residentBoundaryWord,
    copyIndexedWord,copySlice,copyPrefix,copyR,copyStep,unaryProduct,decodeNaturalWord,
    toUnary,hornerIter,udbl,eachSym,transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,uclear,clearWords,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
