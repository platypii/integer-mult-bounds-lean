module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchSetup
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Shared convolution setup is native traffic independent of the batch count;
retiring its generated words never increases stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

theorem batchSetup_native (j : SetupReg → Fin T) :
    mnNativePushBound 3 (batchSetup (P := P) (Q := Q) (A := A) (U := U) j) := by
  simp [batchSetup,operandSetup,unaryProduct,padding,ldrHeader,ldrGamma,ldrPow,ldrLoop,
    ldrStep,ldrHalfFx,ldrBitAct,zeroBits,upow2,udbl,usub,ucopy,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,popPush,dropTop,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

theorem clearWords_native (rs : List (Fin T)) :
    mnNativePushBound 0 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
