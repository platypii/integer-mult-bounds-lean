module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRetainedRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Scalar setup allocates only its bounded header bank; release discards it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

def retainedRoundScalarSetupCost (B p q : ℕ) : ℕ :=
  ((2^15*p+q)*(4*B+10)+2*(8*B+12)+1)+25*(4*B+4)+2*(8*B+8)+2+
    (18+(4*Nat.size (4*p)+31))*tblC B 0

private theorem queue_native (width word saved tmp dst carry : Fin T) (ports : List (Fin T)) :
    mnNativePushBound 13 (binaryHeaderQueue (P := P) (Q := Q) (A := A) (U := U)
      width word saved tmp dst carry ports) := by
  induction ports with
  | nil => simp [binaryHeaderQueue,mnNativePushBound,mnActPush]
  | cons src ports ih =>
    simp [binaryHeaderQueue,ih,prependBinaryHeader,toBinary,bzero,zeroBits,umulSym,eachSym,
      countIter,incrField,incStep,setCarry,moveRightOrdered,moveR,moveStep,
      scanR,drainR,popDo,keepIn,pushN,popPush,whileR,peekR,mnNativePushBound,mnActPush]

private theorem zeroBank_native (width tmp : Fin T) (ports : List (Fin T)) :
    mnNativePushBound 13 (zeroWordBank (P := P) (Q := Q) (A := A) (U := U) width tmp ports) := by
  induction ports with
  | nil => simp [zeroWordBank,mnNativePushBound,mnActPush]
  | cons r ports ih =>
    simp [zeroWordBank,ih,bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

private theorem loadHeaders_native {n : ℕ} (rg : TblR n → Fin T) (src : Fin T) (ports : List (Fin n)) :
    mnNativePushBound 13 (loadBinaryHeaders (P := P) (Q := Q) (A := A) (U := U) rg src ports) := by
  induction ports with
  | nil => simp [loadBinaryHeaders,mnNativePushBound,mnActPush]
  | cons r ports ih =>
    simp [loadBinaryHeaders,loadBinaryHeader,ih,takePrefix,transfer,transferAct,
      moveR,moveStep,uclear,scanR,drainR,popDo,keepIn,whileR,peekR,mnNativePushBound,mnActPush]

theorem installRetainedRoundScalars_native (rg : TblR 25 → Fin T)
    (header word saved tmp carry pSrc qSrc : Fin T) :
    mnNativePushBound 13 (installRetainedRoundScalars (P := P) (Q := Q) (A := A) (U := U)
      rg header word saved tmp carry pSrc qSrc) := by
  have htable (code : TblCode 25) := mnNativePushBound_mono (by decide : 3 ≤ 13)
    (tblCompile_native (P := P) (Q := Q) (A := A) (U := U) rg code)
  exact ⟨⟨queue_native ..,⟨zeroBank_native ..,loadHeaders_native ..⟩⟩,htable _,htable _⟩

theorem generateCyclicNormalizationWidth_native (kernel precision width a h par bits saved : Fin T) :
    mnNativePushBound 13 (generateCyclicNormalizationWidth (P := P) (Q := Q) (A := A) (U := U)
      kernel precision width a h par bits saved) := by
  simp [generateCyclicNormalizationWidth,unarySize,ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,
    umulSym,usub,ucopy,scanR,drainR,popDo,keepIn,pushN,popPush,dropTop,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

theorem releaseScalarBank_native {n : ℕ} (rg : TblR n → Fin T) :
    mnNativePushBound 0 (releaseScalarBank (P := P) (Q := Q) (A := A) (U := U) rg) :=
  clearWords_native _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
