module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCoreGather
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Uniform stock for the generated restoring class sweep. Native stream and
controller work is bounded by its actual runtime, using the structural table
certificate rather than expanding the concrete controller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Host.SS
open IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type}

private theorem clearWords_native_three (rs : List (Fin T)) :
    mnNativePushBound 3 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

private theorem chirpBankCopies_native (width savedWidth savedSource buf : Fin T)
    (rs : List (Fin T × Fin T)) :
    mnNativePushBound 3 (chirpBankCopies (P := P) (Q := Q) (A := A) (U := U)
      width savedWidth savedSource buf rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [padCopy,padStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush],ih⟩

private theorem chirpBankLoad_native {n : ℕ} (rg : TblR n → Fin T)
    (source : Fin n → Fin T) (width symbols : Fin T) :
    mnNativePushBound 3 (chirpBankLoad (P := P) (Q := Q) (A := A) (U := U) rg source width symbols) := by
  unfold chirpBankLoad
  refine ⟨?_,?_,chirpBankCopies_native _ _ _ _ _⟩
  all_goals simp [ucopy,umulSym,scanR,drainR,popDo,whileR,keepIn,pushN,moveR,moveStep,peekR,mnNativePushBound,mnActPush]

private theorem generatedCoreGather_native :
    mnNativePushBound 3 (generatedCoreGather (P := P) (Q := Q) (A := A) (U := U)) := by
  simp only [generatedCoreGather,generatedCoreControls,generatedCoreCountedHost,countedOriginHost,
    preparedNaturalAdvanceControls,initializeAdvanceBank,mnNativePushBound]
  refine ⟨⟨⟨tblCompile_native _ _,?_,?_⟩,clearWords_native_three _,
    chirpBankLoad_native _ _ _ _,?_,?_,clearWords_native_three _⟩,?_⟩
  all_goals simp [originAdvanceControls,originAdvanceLoopBody,
    originAdvanceNext,chirpControlEmit,countWords,countWordsBody,tblLoad1,toBinary,toUnary,
    hornerIter,udbl,eachSym,zeroBits,countIter,incrField,incStep,setCarry,bclear,bzero,
    naturalGather,gatherOffset,gatherBatch,gatherLoopBody,gatherPacket,gatherNext,gatherRead,
    gatherReadStep,WordCmd.peekRp,copyPrefix,copyR,copyStep,transfer,transferAct,unaryProduct,
    ucopy,umulSym,scanP,popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush,tblCompile_native]

theorem restoredCoreGather_native :
    mnNativePushBound 3 (restoredCoreGather (P := P) (Q := Q) (A := A) (U := U)) := by
  change mnNativePushBound 3 (.seq (.seq prepareCoreGatherHeaders
    (.seq preparedCoreGather (clearWords [103,115]))) (clearWords [91,109,116]))
  refine ⟨⟨?_,⟨chirpBankLoad_native _ _ _ _,embProg_native _ _ _ generatedCoreGather_native⟩,
    clearWords_native_three _⟩,clearWords_native_three _⟩
  simp [prepareCoreGatherHeaders,toUnary,hornerIter,udbl,eachSym,ucopy,umulSym,
    popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

variable {body : P → Pr P 168 Q A U}

theorem restoredCoreGather_exec_within {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (C : ZMod s → GaussianInt) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hsource : S.R 110 = cstream A w (chirpLine s C))
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = []) (horigin : S.R 109 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ restoredCoreGatherCost V s width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*restoredCoreGatherCost V s width radius L w) depth restoredCoreGather (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R 108
          (cstream A w (coreGatherPayload width radius L [C]) ++ S.R 108))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := restoredCoreGather_exec (body := body)
    hwidth hwide hLfit hwV hvol hA hVpos hgroup C v S h163 h115 h103 h105
    hs hw hr hL hz hblank h104 h106 h116 hsource hword hcontrol horigin hclean hfresh
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3 restoredCoreGather_native depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
