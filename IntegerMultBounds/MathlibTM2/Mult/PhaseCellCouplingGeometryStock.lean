module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCouplingGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock

/-! Shared geometry uses native binary operations with a fixed push bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

theorem binaryHeaderBank_native (width tmp scratch carry : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 3 (binaryHeaderBank (P := P) (Q := Q) (A := A) (U := U) width tmp scratch carry rs) := by
  induction rs with
  | nil => simp [binaryHeaderBank,mnNativePushBound,mnActPush]
  | cons p rs ih =>
    simp only [binaryHeaderBank,mnNativePushBound]
    refine ⟨?_,ih⟩
    simp [toBinary,eachSym,bzero,popPush,zeroBits,countIter,incrField,incStep,setCarry,
      umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]

theorem generateCouplingGeometry_native :
    mnNativePushBound 3 (generateCouplingGeometry (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [generateCouplingGeometry,binaryHeaderBank_native,completeCouplingIntervalMetadata,
    bsub,badd,bcopy,bzero,zipKeep,zipPass,zipStep,zipInit,zeroBits,
    umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
