module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizePlan
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! A native stock certificate for the reused normalization/publication routine.
Scalar programs remain abstract; lists of input words are handled structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

private theorem table_native13 {n : ℕ} (rg : TblR n → Fin T) (code : TblCode n) :
    mnNativePushBound 13 (tblCompile (P := P) (Q := Q) (A := A) (U := U) rg code) :=
  mnNativePushBound_mono (by decide) (tblCompile_native rg code)

private theorem copies_native13 {n : ℕ} (rg : TblR n → Fin T) (rs : List (Fin n × Fin T)) :
    mnNativePushBound 13 (tblUnaryCopies (P := P) (Q := Q) (A := A) (U := U) rg rs) :=
  mnNativePushBound_mono (by decide) (tblUnaryCopies_native rg rs)

private theorem clear_native13 (rs : List (Fin T)) :
    mnNativePushBound 13 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) :=
  mnNativePushBound_mono (by decide) (ShortConv.clearWords_native rs)

private theorem zero_bank_native13 (width tmp : Fin T) (rs : List (Fin T)) :
    mnNativePushBound 13 (zeroWordBank (P := P) (Q := Q) (A := A) (U := U) width tmp rs) := by
  induction rs with
  | nil => simp [zeroWordBank,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    simp [zeroWordBank,ih,bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

private theorem load_headers_native13 {n : ℕ} (rg : TblR n → Fin T) (src : Fin T) (rs : List (Fin n)) :
    mnNativePushBound 13 (loadBinaryHeaders (P := P) (Q := Q) (A := A) (U := U) rg src rs) := by
  induction rs with
  | nil => simp [loadBinaryHeaders,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    simp [loadBinaryHeaders,loadBinaryHeader,ih,takePrefix,transfer,transferAct,
      moveR,moveStep,uclear,scanR,drainR,popDo,keepIn,whileR,peekR,mnNativePushBound,mnActPush]

theorem RecoveryNormalizePlan.native (plan : RecoveryNormalizePlan T) :
    mnNativePushBound 13 (plan.program (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [RecoveryNormalizePlan.program,ordinaryNormalizePackedBatch,installInverseParameters,installScalarInputs,
    initializeScalarBank,zero_bank_native13,load_headers_native13,releaseScalarBank,clear_native13,
    preparedNormalizePackedBatch,table_native13,copies_native13,normalizePackedBatch,
    roundPackedKey,roundPackedPrefix,generatedFinalRound,generatedRoundHeaders,installRoundHeaders,
    publishRoundedKey,generateDoubleWidth,widenPackedKey,widenPackedPrefix,generatedWidenPackets,withWidthDifference,
    transformPrefix,topPass,topWords,topShiftWord,Shift.counted,Shift.copyStep,topSignAct,topAbsF,topEmitF,topEndAct,
    topWidenWord,topDupF,unaryProduct,ucopy,usub,dropTop,umulSym,transfer,transferAct,moveR,moveStep,
    uclear,scanP,scanR,drainR,popDo,keepIn,whileR,peekR,pushN,popPush,mnNativePushBound,mnActPush]

theorem RecoveryNormalizePlan.finished_native (plan : RecoveryNormalizePlan T) :
    mnNativePushBound 13 (plan.finishedProgram (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨plan.native,?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem RecoveryNormalizePlan.within_stock {body : P → Pr P T Q A U} (plan : RecoveryNormalizePlan T)
    {v v' : HS T Q A U} {S F : Stacks T A} {n cost : ℕ}
    (hex : Exec body plan.program (Host.mk v S) n (Host.mk v' F)) (hn : n ≤ cost) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+13*cost)
      depth plan.program (Host.mk v S) n (Host.mk v' F) :=
  mn_native_exec_within hex 13 plan.native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
