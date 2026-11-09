module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Runtime width and inverse-parser packets use only linear native header traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generateRuntimeWidth_native :
    mnNativePushBound 8 (generateRuntimeWidth (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateRuntimeWidth,umul,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem saveBatchInverseHeader_native :
    mnNativePushBound 2 (saveBatchInverseHeader (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [saveBatchInverseHeader,copyR,copyStep,clearWords,uclear,drainR,popDo,
    pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem generateRuntimeWidth_exec_within (q : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q) (h94 : S.R 94 = []) (h104 : S.R 104 = []) :
    ∃ v', v'.user = v.user ∧ (∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+8*(4*q+5)) depth generateRuntimeWidth (mk v S) (4*q+5)
      (mk v' { S with R := Function.update S.R 94 (List.replicate (2*q+8) tick) }) ) := by
  obtain ⟨v',hu,he⟩ := generateRuntimeWidth_exec (body := body) q v S hq h94 h104
  exact ⟨v',hu,fun depth => mn_native_exec_within he 8 generateRuntimeWidth_native depth _ (by omega)⟩

theorem saveBatchInverseHeader_exec_within (B w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : S.R 116 = List.replicate B tick) (hw : (S.R 94).length = w) (h107 : S.R 107 = []) :
    ∃ v', v'.user = v.user ∧ (∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(6*B+2*w+10)) depth saveBatchInverseHeader (mk v S) (6*B+2*w+10)
      (mk v' { S with R := (Function.update (Function.update (Function.update S.R
        109 (List.replicate B tick ++ blank :: S.R 109)) 94 []) 116 []) }) ) := by
  obtain ⟨v',hu,he⟩ := saveBatchInverseHeader_exec (body := body) B w v S hB hw h107
  exact ⟨v',hu,fun depth => mn_native_exec_within he 2 saveBatchInverseHeader_native depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
