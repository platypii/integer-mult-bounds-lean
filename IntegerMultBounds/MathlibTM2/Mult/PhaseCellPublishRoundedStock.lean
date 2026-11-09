module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRoundedBatch
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Common-width publication uses a fixed native push bound. Its existing cost
is linear in the encoded payload and the generated counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem publishRoundedKey_native (precision wide width replicas rows rowWidth count src work saved tmp extra : Fin T) :
    mnNativePushBound 13 (publishRoundedKey (P := P) (Q := Q) (A := A) (U := U)
      precision wide width replicas rows rowWidth count src work saved tmp extra) := by
  simp [publishRoundedKey,generateDoubleWidth,widenPackedKey,widenPackedPrefix,generatedWidenPackets,
    withWidthDifference,transformPrefix,topPass,topWords,topWidenWord,topDupF,Shift.counted,Shift.copyStep,
    unaryProduct,ucopy,usub,dropTop,umulSym,transfer,transferAct,moveR,moveStep,
    uclear,scanP,scanR,drainR,popDo,keepIn,whileR,peekR,pushN,popPush,mnNativePushBound,mnActPush]

/-- Publication traffic is linear in the encoded payload and one row of counters. -/
theorem publishRoundedKeyCost_le (p W N L : ℕ) (hW : 2*p+13 ≤ W) :
    publishRoundedKeyCost p W N L ≤ (N+1)*(L+1)*(40*W+80) := by
  unfold publishRoundedKeyCost widenPackedKeyCost widenPackedPrefixCost
  dsimp only
  have hsub : W-(2*p+13) ≤ W := Nat.sub_le _ _
  have hrow := Nat.mul_le_mul_left L hW
  have hbatch := Nat.mul_le_mul_left (N*L) hW
  nlinarith [Nat.zero_le (N*L*W),Nat.zero_le (N*L),Nat.zero_le (N*W),Nat.zero_le (L*W)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
