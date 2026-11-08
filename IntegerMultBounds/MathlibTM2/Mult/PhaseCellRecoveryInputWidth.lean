module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Regenerate the cropped packet byte ruler from the rounding setup's binary
word width and retained row count. The binary source and row ruler restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def recoveryInputWidth (binary rows width dst work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary binary width work saved tmp)
    (.seq (unaryProduct rows width dst saved tmp) (uclear width))

def recoveryInputWidthCost (B L w : ℕ) : ℕ :=
  (6*w+11*B+6)+(L*(4*w+9)+4)+(2*w+2)

theorem recoveryInputWidth_native (binary rows width dst work saved tmp : Fin T) :
    mnNativePushBound 2 (recoveryInputWidth (P := P) (Q := Q) (A := A) (U := U)
      binary rows width dst work saved tmp) := by
  refine ⟨?_,unaryProduct_native ..,?_⟩
  · simp [toUnary,eachSym,hornerIter,udbl,moveR,moveStep,whileR,drainR,pushN,popDo,peekR,
      popPush,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem recoveryInputWidth_exec (binary rows width dst work saved tmp : Fin T)
    (hreg : [binary,rows,width,dst,work,saved,tmp].Nodup)
    (B L w : ℕ) (hw : w < 2^B) (v : HS T Q A U) (S : Stacks T A)
    (hbinary : S.R binary = binSyms B w) (hrows : (S.R rows).length = L)
    (hblank : ∀ i ∈ [width,dst,work,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryInputWidthCost B L w ∧
      Exec body (recoveryInputWidth binary rows width dst work saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R dst (List.replicate (L*w) tick)}) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*recoveryInputWidthCost B L w) depth
        (recoveryInputWidth binary rows width dst work saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R dst (List.replicate (L*w) tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear body
    (by regs_nodup : [binary,width,work,saved,tmp].Nodup) hw v S hbinary
    (hblank work (by simp)) (hblank saved (by simp)) (hblank tmp (by simp))
  let F : Stacks T A := {S with R := Function.update S.R width (List.replicate w tick)}
  have he₁' : Exec body (toUnary binary width work saved tmp) (Host.mk v S) n₁ (Host.mk v₁ F) := by
    simpa only [hblank width (by simp),List.append_nil,F] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (by regs_nodup : [rows,width,dst,saved,tmp].Nodup) v₁ F
    (by simpa [F,‹width ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [F,‹width ≠ tmp›.symm] using hblank tmp (by simp))
  have hn₂' : n₂ ≤ L*(4*w+9)+4 := by
    simpa only [F,Function.update_of_ne ‹rows ≠ width›,Function.update_self,List.length_replicate,hrows] using hn₂
  let G : Stacks T A := {F with R := Function.update F.R dst (List.replicate (L*w) tick)}
  have he₂' : Exec body (unaryProduct rows width dst saved tmp) (Host.mk v₁ F) n₂ (Host.mk v₂ G) := by
    simpa only [G,F,Function.update_of_ne ‹rows ≠ width›,Function.update_of_ne ‹width ≠ dst›.symm,
      Function.update_self,List.length_replicate,hrows,hblank dst (by simp),List.append_nil] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) width v₂ G
  have hlen : (G.R width).length = w := by simp [G,F,‹width ≠ dst›]
  have hfinal : {G with R := Function.update G.R width []} =
      {S with R := Function.update S.R dst (List.replicate (L*w) tick)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = width
    · subst i; simp [‹width ≠ dst›,hblank width (by simp)]
    · simp [G,F,Function.update_apply,hi]
  rw [hlen,hfinal] at he₃
  have hn : n₁+(n₂+(2*w+2)) ≤ recoveryInputWidthCost B L w := by
    unfold recoveryInputWidthCost
    omega
  have hex : Exec body (recoveryInputWidth binary rows width dst work saved tmp)
      (Host.mk v S) (n₁+(n₂+(2*w+2)))
      (Host.mk v₃ {S with R := Function.update S.R dst (List.replicate (L*w) tick)}) :=
    Exec.seq he₁' (Exec.seq he₂' he₃)
  exact ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,hex,fun depth =>
    mn_native_exec_within hex 2 (recoveryInputWidth_native ..) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
