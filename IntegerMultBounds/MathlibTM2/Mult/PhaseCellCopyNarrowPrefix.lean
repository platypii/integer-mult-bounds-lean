module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

/-- Isolate a counted common-width prefix, then resize only the copy. The
retained source and its arbitrary borrowed suffix survive verbatim. -/
def copyNarrowPrefix (count src dst saved tmp wide width work zero extra : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix count src dst saved tmp) (generatedNarrowPackets wide width dst work zero extra tmp)

def copyNarrowPrefixCost (W w N : ℕ) : ℕ :=
  (10*(N*W)+10)+(4*W+4*w+2*(W-w)+(N*(4*W+2*w+14)+4)+10)

theorem copyNarrowPrefix_exec (body : P → Pr P T Q A U)
    (count src dst saved tmp wide width work zero extra : Fin T)
    (hreg : [count,src,dst,saved,tmp,wide,width,work,zero,extra].Nodup)
    (W w : ℕ) (hW : 1 ≤ W) (hw : w ≤ W) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A W xs++tail) (hcount : (S.R count).length = xs.length*W)
    (hwide : (S.R wide).length = W) (hwidth : (S.R width).length = w)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hwork : S.R work = []) (hzero : S.R zero = []) (hextra : S.R extra = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyNarrowPrefix count src dst saved tmp wide width work zero extra) (mk v S)
        (copyNarrowPrefixCost W w xs.length)
        (mk v' {S with R := Function.update S.R dst (cstream A w xs)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body) (count := count) (src := src) (dst := dst)
    (saved := saved) (tmp := tmp) (by regs_nodup) v S (cstream A W xs) tail hsrc
    (by simpa only [length_cstream] using hcount) hsaved htmp
  rw [hdst,List.append_nil,length_cstream] at he₁
  let M : Stacks T A := {S with R := Function.update S.R dst (cstream A W xs)}
  obtain ⟨v₂,hu₂,he₂⟩ := generatedNarrowPackets_exec (body := body) (wide := wide) (width := width)
    (src := dst) (dst := work) (zero := zero) (extra := extra) (tmp := tmp) (by regs_nodup) W w hW hw xs v₁ M
    (by simpa [M,‹dst ≠ wide›.symm] using hwide)
    (by simpa [M,‹dst ≠ width›.symm] using hwidth)
    (by simp [M])
    (by simpa [M,‹dst ≠ work›.symm] using hwork)
    (by simpa [M,‹dst ≠ zero›.symm] using hzero)
    (by simpa [M,‹dst ≠ extra›.symm] using hextra)
    (by simpa [M,‹dst ≠ tmp›.symm] using htmp)
  simp only [M,Function.update_idem] at he₂
  exact ⟨v₂,hu₂.trans hu₁,Exec.seq he₁ he₂⟩

theorem copyNarrowPrefix_native (count src dst saved tmp wide width work zero extra : Fin T) :
    mnNativePushBound 3
      (copyNarrowPrefix (P := P) (Q := Q) (A := A) (U := U) count src dst saved tmp wide width work zero extra) := by
  simp [copyNarrowPrefix,copyPrefix,generatedNarrowPackets,withWidthDifference,ucopy,umulSym,usub,
    dropTop,topPass,topWords,floorSliceWord,transfer,transferAct,copyR,copyStep,moveR,moveStep,
    scanR,drainR,popDo,keepIn,whileR,peekR,uclear,pushN,popPush,mnNativePushBound,mnActPush]

theorem copyNarrowPrefix_exec_within (body : P → Pr P T Q A U)
    (count src dst saved tmp wide width work zero extra : Fin T)
    (hreg : [count,src,dst,saved,tmp,wide,width,work,zero,extra].Nodup)
    (W w : ℕ) (hW : 1 ≤ W) (hw : w ≤ W) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A W xs++tail) (hcount : (S.R count).length = xs.length*W)
    (hwide : (S.R wide).length = W) (hwidth : (S.R width).length = w)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hwork : S.R work = []) (hzero : S.R zero = []) (hextra : S.R extra = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*copyNarrowPrefixCost W w xs.length) depth
        (copyNarrowPrefix count src dst saved tmp wide width work zero extra) (mk v S)
        (copyNarrowPrefixCost W w xs.length)
        (mk v' {S with R := Function.update S.R dst (cstream A w xs)}) := by
  obtain ⟨v',hu,he⟩ := copyNarrowPrefix_exec body count src dst saved tmp wide width work zero extra hreg
    W w hW hw xs tail v S hsrc hcount hwide hwidth hdst hsaved htmp hwork hzero hextra
  exact ⟨v',hu,mn_native_exec_within he 3 (copyNarrowPrefix_native ..) depth
    (mnSize (mk v S)+depth+3*copyNarrowPrefixCost W w xs.length) (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
