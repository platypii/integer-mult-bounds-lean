module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPrepare
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock

/-! Weight readiness and routing use native traffic; counter retirement adds
no stock. The shared numerical reserve comes from the pointwise stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem one_push_le_cmulBlock {T : ℕ} (rg : CR → Fin T) (prog : Pr P T Q A U) :
    mnProgPush prog ≤ mnProgPush (cmulBlock rg prog) := by
  change mnProgPush prog ≤ max (max _ (max (mnProgPush prog) _)) _
  exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem routeWeights_native :
    mnNativePushBound 3 (routeWeights (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [routeWeights,branchWords,halfCount,halfPairAct,takePrefix,unaryProduct,
    copyPrefix,copyR,copyStep,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,
    popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem prepareWeights_native :
    mnNativePushBound 3 (prepareWeights (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [prepareWeights,prepare_native,releasePrefix,copyR,copyStep,transfer,transferAct,
    scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

theorem releaseWeightCounters_native :
    mnNativePushBound 0 (releaseWeightCounters (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [releaseWeightCounters,clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
