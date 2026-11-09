module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Ordinary unary geometry is converted to table headers by native linear traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type}

theorem generateSetupWidth_native :
    mnNativePushBound 5 (generateSetupWidth (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateSetupWidth,popPush,unaryProduct,umul,uadd,ucopy,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem generateCoefficientWidth_native :
    mnNativePushBound 16 (generateCoefficientWidth (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateCoefficientWidth,unarySize,ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,
    umul,ucopy,umulSym,uclear,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem loadCoefficientListLinear_native (rs : List (Fin 117 × Fin 48)) :
    mnNativePushBound 3 (loadCoefficientListLinear (P₀ := P₀) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    refine ⟨?_,ih⟩
    simp [tblLoadLinear,unaryBinaryWidth,unaryBinary,bwiden,bclear,
      ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,usub,dropTop,bpad,
      ucopy,umulSym,uclear,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem prepareCoefficientHeaders_native :
    mnNativePushBound 3 (prepareCoefficientHeaders (P₀ := P₀) (Q := Q) (A := A) (U := U)) :=
  ⟨chirpBankLoad_native _ _ _ _,loadCoefficientListLinear_native _,clearWords_native_three _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
