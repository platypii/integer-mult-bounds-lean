module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparePublicationControls
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Control preparation is native stream work with at most two pushes per
atomic action. Its movement bill also bounds intermediate stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem preparePublicationControls_pushBound
    (remainder count coreWidth wordWidth product fullControl clippedControl saved tmp : Fin T) :
    mnNativePushBound 2 (preparePublicationControls (P := P) (Q := Q) (A := A) (U := U)
      remainder count coreWidth wordWidth product fullControl clippedControl saved tmp) := by
  simp [preparePublicationControls,remainderPublicationControls,clippedCorePublicationControls,
    unaryProduct,scanP,ucopy,umulSym,transfer,copyR,moveR,uclear,
    keepIn,scanR,transferAct,copyStep,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
