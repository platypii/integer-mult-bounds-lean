module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrdinaryCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Coefficient-page setup is native shared work. Its syntactic push certificate
is independent of endpoint dimensions and the number of coefficient rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type}

private theorem tblCompile_native24 {n T : ℕ} (rg : TblR n → Fin T) (code : TblCode n) :
    mnNativePushBound 24 (tblCompile (P := P) (Q := Q) (A := A) (U := U) rg code) :=
  mnNativePushBound_mono (by decide) (tblCompile_native rg code)

private theorem clearWords_native24 {T : ℕ} (rs : List (Fin T)) :
    mnNativePushBound 24 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) :=
  mnNativePushBound_mono (by decide) (clearWords_native_three rs)

private theorem chirpBankLoad_native24 {n T : ℕ} (rg : TblR n → Fin T)
    (source : Fin n → Fin T) (width symbols : Fin T) :
    mnNativePushBound 24 (chirpBankLoad (P := P) (Q := Q) (A := A) (U := U) rg source width symbols) :=
  mnNativePushBound_mono (by decide) (chirpBankLoad_native rg source width symbols)

theorem buildMarkedRowCoefficientPacket_native :
    mnNativePushBound 24 (buildMarkedRowCoefficientPacket (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [buildMarkedRowCoefficientPacket,generateLiftedCoefficientWidth,buildPreparedRowPacket,
    publishMarkedWidth,initializeRowCoefficientHeaders,publishPreparedRowPacket,
    addUnarySizes,liftedWidthSources,unarySize,loadRowCoefficientList,rowCoefficientHeaders,publishBinaryHeaders,preparedRowPacketFields,
    initializeRowCoefficientBank,chirpBankLoad_native24,tblLoad1,toBinary,bzero,zeroBits,eachSym,countIter,incrField,incStep,setCarry,
    ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,bclear,tblHost,tblCompile_native24,clearWords_native24,copyPrefix,copyR,copyStep,transfer,transferAct,
    ucopy,umul,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem markedRowCoefficient_native :
    mnNativePushBound 24 (markedRowCoefficient (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [markedRowCoefficient,takeMarkedWidth,publishMarkedWidth,rowCoefficientPacketStep,
    markedWidthPeek,markedWidthStep,borrowBinaryHeaders,preparedRowPacketFields,takePrefix,transfer,transferAct,
    countIter,incrField,incStep,setCarry,rowCoefficientFromPacket,initializeRowCoefficientBank,chirpBankLoad_native24,
    advanceBinaryPacket,borrowPreparedRowPacket,rowCoefficientHost,loadBinaryHeaders,loadBinaryHeader,umul,copyPrefix,copyR,copyStep,
    tblHost,tblCompile_native24,clearWords_native24,
    ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

private theorem intervalGuard_native24 (boundary : Bool) :
    mnNativePushBound 24 (.seq (loadIntervalGuardBank (P := P) (Q := Q) (A := A) (U := U)) (recoveryGuardIntervalHost boundary)) := by
  simp [loadIntervalGuardBank,chirpBankLoad_native24,recoveryGuardIntervalHost,intervalGuardStreamHost,
    releaseIntervalGuardBank,tblHost,tblCompile_native24,clearWords_native24,
    moveR,moveStep,whileR,peekR,uclear,drainR,popDo,mnNativePushBound,mnActPush]

private theorem finishCouplingCoefficientInterval_native24 :
    mnNativePushBound 24 (finishCouplingCoefficientInterval (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [finishCouplingCoefficientInterval,couplingCoefficientPageLoop,countedLoop,countedLoopBody,
    couplingCoefficientPageStep,couplingCoefficientPageRow,prepareCouplingCoefficientRow,
    retainedCouplingCoefficients,embProg_native,markedRowCoefficient_native,
    advanceMarkedBinaryPacket,takeMarkedWidth,markedWidthPeek,markedWidthStep,publishMarkedWidth,
    advanceBinaryPacket,takePrefix,countIter,incrField,incStep,setCarry,transferCountedLine,unaryProduct,
    transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem ordinaryCouplingCoefficientInterval_native :
    mnNativePushBound 24 (ordinaryCouplingCoefficientInterval (P := P) (Q := Q) (A := A) (U := U)) := by
  apply embProg_native
  change mnNativePushBound 24 (.seq (ucopy 141 107 135)
    (.seq (embProg sharedCouplingReg Empty.elim (binaryLengthCouplingCoefficientInterval (P := Empty))) (uclear 107)))
  refine ⟨?_,⟨embProg_native sharedCouplingReg Empty.elim _ ?_,?_⟩⟩
  · simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · simp [binaryLengthCouplingCoefficientInterval,preparedCouplingCoefficientInterval,
      countedCouplingCoefficientInterval,guardedCouplingCoefficientInterval,placedPrepareCouplingIntervalPacket,
      prepareRetainedCouplingPacket,embProg_native,buildMarkedRowCoefficientPacket_native,
      placedBinaryRecoveryGuardInterval,placedFinishCouplingCoefficientInterval,
      finishCouplingCoefficientInterval_native24,prepareCouplingPageCountsOn,
      toUnary,hornerIter,udbl,eachSym,ucopy,umul,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,
      moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]
    exact embProg_native intervalGuardPlacement Empty.elim _ (intervalGuard_native24 true)
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
