module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock

/-! Coupling counter setup is native shared work with a fixed push bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.WordCmd IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type}

theorem couplingReadiness_native :
    mnNativePushBound 3 (couplingReadiness (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [couplingReadiness,withSavedHeader,couplingReadinessCore,prepare_native,
    moveRL,rlStep,peekRp,actThen,mv1,moveLR,lrStep,WordCmd.peekL,
    ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
