module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherStock

/-! Cache copying and local gather preparation use native stream work only.
Their linear traffic ledger bounds every intermediate store, including the
retained source, numerical cache and all spectator banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem retainedRowGather_native (replicas saved count source archive dst control savedControl advance
    window src acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) :
    mnNativePushBound 3 (retainedRowGather (P := P) (Q := Q) (A := A) (U := U)
      replicas saved count source archive dst control savedControl advance window src acc current
      savedSource buf tmp initialControl initialSource rowCount wordR) := by
  simp [retainedRowGather,restoringRowScan,retainedRowGatherStep,takeCopyPrefix,
    naturalGather,gatherOffset,gatherBatch,gatherLoopBody,gatherPacket,gatherNext,gatherRead,
    gatherReadStep,WordCmd.peekRp,copyPrefix,copyR,copyStep,transfer,transferAct,unaryProduct,
    ucopy,umulSym,scanP,popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

private theorem preparedNaturalAdvanceControls_native :
    mnNativePushBound 3 (preparedNaturalAdvanceControls (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  unfold preparedNaturalAdvanceControls
  refine ⟨chirpBankLoad_native _ _ _ _,?_,?_,?_⟩
  · simp [tblLoad1,toBinary,eachSym,zeroBits,countIter,incrField,incStep,setCarry,bclear,bzero,
      umulSym,scanR,drainR,popDo,popPush,keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,
      mnNativePushBound,mnActPush]
  · simp [originAdvanceControls,originAdvanceLoopBody,originAdvanceNext,chirpControlEmit,
      toUnary,hornerIter,udbl,eachSym,copyPrefix,copyR,copyStep,transfer,transferAct,
      popPush,scanR,keepIn,drainR,popDo,pushN,moveR,moveStep,whileR,peekR,uclear,
      mnNativePushBound,mnActPush,tblCompile_native]
  · simp [releaseAdvanceBank,clearWords_native_three]

theorem sharedPackedReplicaGather_native :
    mnNativePushBound 3 (sharedPackedReplicaGather (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨embProg_native _ _ _ preparedNaturalAdvanceControls_native,
    retainedRowGather_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

namespace ScalarPlacement

private theorem replicateWeightPage_native :
    mnNativePushBound 3 (replicateWeightPage (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [replicateWeightPage,repeatWeightBanks,repeatPrefix,packRepeatedWeights,packWeightBatch,reverseWords,reverseLoopBody,reverseNext,
    releasePrefix,unaryProduct,copyPrefix,copyR,copyStep,
    transfer,transferAct,ucopy,umulSym,scanP,popPush,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem prepareReplicaInteriorCache_native :
    mnNativePushBound 3 (prepareReplicaInteriorCache (P := P) (Q := Q) (A := A) (U := U)) := by
  change mnNativePushBound 3 (.seq (.seq (embProg weightCacheCoreReg Empty.elim replicateWeightPage)
    cacheWeightPageFromDimensions) prepareReplicaSolverDimensions)
  refine ⟨⟨embProg_native _ _ _ replicateWeightPage_native,?_⟩,?_⟩
  all_goals simp [cacheWeightPageFromDimensions,cacheWeightPage,prepareReplicaSolverDimensions,
    replaceUnary,takePrefix,unaryProduct,clearWords,
    transfer,transferAct,ucopy,umulSym,scanP,popPush,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem gatheredReplicaInteriorPreparation_native (plan : ReplicaInteriorPlacement T) :
    mnNativePushBound 3 (gatheredReplicaInteriorPreparation (P := P) (Q := Q) (A := A) (U := U) plan) :=
  ⟨embProg_native _ _ _ prepareReplicaInteriorCache_native,
    embProg_native _ _ _ sharedPackedReplicaGather_native⟩

/-- This is a stock certificate for the same actual preparation execution.
The complete initial store, including every inactive bank, is counted once. -/
theorem gatheredReplicaInteriorPreparation_within (plan : ReplicaInteriorPlacement T)
    {N B V span L w steps : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (gatheredReplicaInteriorPreparation plan) z steps z')
    (hn : steps ≤ prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B)
    (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      3*(prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B))
      depth (gatheredReplicaInteriorPreparation plan) z steps z' :=
  mn_native_exec_within he 3 (gatheredReplicaInteriorPreparation_native plan) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn) _)

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
