module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryRow
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Native boundary projection only rearranges and copies symbols. A fixed
atomic push bound converts its linear per-row time into a per-row reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem bandUnfoldLineP_native (rg : RsbR → Fin T) :
    mnNativePushBound 4 (bandUnfoldLineP (P := P) (Q := Q) (A := A) (U := U) rg) := by
  simp [bandUnfoldLineP,bandDeILeaveP,bandRec1P,bandRevP,rsbRep,rsbScanIf,
    rsbMv,rsbMvTop,scanR,drainR,popDo,keepIn,moveR,whileR,moveStep,peekR,popPush,
    mnNativePushBound,mnActPush]

theorem generatedBoundaryRealUnfold_native :
    mnNativePushBound 4 (generatedBoundaryRealUnfold (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [generatedBoundaryRealUnfold,generatedBoundaryUnfold,boundaryUnfoldCounters,
    bandUnfoldLineP_native,boundaryRealProjection,realPrefix,unaryProduct,transfer,transferAct,
    clearWords,udiv,usub,uclear,ucopy,umulSym,scanP,scanR,keepIn,pushN,
    drainR,popDo,divChain,dropTop,moveR,whileR,moveStep,peekR,popPush,mnNativePushBound,mnActPush]

theorem sharedPageBoundaryRealUnfold_native :
    mnNativePushBound 4 (sharedPageBoundaryRealUnfold (P := P) (Q := Q) (A := A) (U := U)) :=
  embProg_native _ _ _ generatedBoundaryRealUnfold_native

theorem nativeCyclicBoundaryRow_native :
    mnNativePushBound 4 (nativeCyclicBoundaryRow (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [nativeCyclicBoundaryRow,nativeCyclicBoundaryRecovery,residualBatchRecoveryInput,
    sharedPageBoundaryRealUnfold_native,nativeCyclicBoundaryPieces,placedPackedBoundaryPublish,
    spreadRecords,spreadRecordStep,eachSym,retireCountedLine,discardPrefix,unaryProduct,
    copyPrefix,transfer,transferAct,uclear,ucopy,umulSym,scanP,scanR,keepIn,pushN,
    drainR,popDo,copyStep,copyR,moveR,whileR,moveStep,peekR,popPush,mnNativePushBound,mnActPush]

theorem nativeCyclicBoundaryRow_workspace_le (N n w : ℕ) :
    4*nativeCyclicBoundaryRowCost N n w ≤ 1000*(N+n+1)*(w+1) := by
  dsimp [nativeCyclicBoundaryRowCost,residualBatchRecoveryInputCost,
    generatedBoundaryUnfoldCost,retireCountedLineCost]
  nlinarith only [Nat.zero_le (N*w),Nat.zero_le (n*w)]

/-- A single row needs a linear reserve. A batch can reuse it after bounding
the stock at iteration boundaries independently of the row workspace. -/
theorem nativeCyclicBoundaryRow_exec_within_of_exec {body : P → Pr P 240 Q A U}
    {v vf : HS 240 Q A U} {S F : Stacks 240 A} {steps N n w : ℕ}
    (he : Exec body nativeCyclicBoundaryRow (mk v S) steps (mk vf F))
    (htime : steps ≤ nativeCyclicBoundaryRowCost N n w) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      4*nativeCyclicBoundaryRowCost N n w) depth
      nativeCyclicBoundaryRow (mk v S) steps (mk vf F) := by
  apply mn_native_exec_within he 4 nativeCyclicBoundaryRow_native depth _
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
