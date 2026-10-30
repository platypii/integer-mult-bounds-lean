module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidth

/-! Generate and dispose the difference of retained packet-width headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def withWidthDifference (wide width extra tmp : Fin T) (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy wide extra tmp) (.seq (usub width extra tmp) (.seq run (uclear extra)))

/-- The conversion body sees a generated width difference and restores it.
The wrapper removes it and restores the original caller frame. -/
theorem withWidthDifference_exec {wide width extra tmp src : Fin T}
    (hreg : [wide,width,extra,tmp,src].Nodup) (run : Pr P T Q A U)
    (W w cost : ℕ) (ys : List (Fin (A+4)))
    (S : Stacks T A) (hwide : (S.R wide).length = W)
    (hwidth : (S.R width).length = w) (hextra : S.R extra = []) (htmp : S.R tmp = [])
    (hrun : ∀ v : HS T Q A U,
      ∃ v', v'.user = v.user ∧
        Exec body run
          (mk v {S with R := Function.update S.R extra (List.replicate (W-w) tick)}) cost
          (mk v' {S with R := (Function.update (Function.update S.R extra
            (List.replicate (W-w) tick)) src ys)}))
    (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧
      Exec body (withWidthDifference wide width extra tmp run) (mk v S)
        (4*W+4*w+2*(W-w)+cost+10)
        (mk v' {S with R := Function.update S.R src ys}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹wide ≠ extra› ‹wide ≠ tmp›
    ‹extra ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R extra (List.replicate W tick)}
  have he₁' : Exec body (ucopy wide extra tmp) (mk v S) (4*W+4) (mk v₁ S₁) := by
    simpa [S₁,hwide,hextra] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) ‹width ≠ extra› ‹width ≠ tmp›
    ‹extra ≠ tmp› v₁ S₁ (by simp [S₁,‹extra ≠ tmp›.symm,htmp])
  let S₂ : Stacks T A := {S with R := Function.update S.R extra (List.replicate (W-w) tick)}
  have he₂' : Exec body (usub width extra tmp) (mk v₁ S₁) (4*w+4) (mk v₂ S₂) := by
    simpa [S₁,S₂,‹width ≠ extra›,hwidth] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := hrun v₂
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R src ys}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) extra v₃ S₃
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,‹extra ≠ src›]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = src
    · subst i; simp [S₃,S₂,‹extra ≠ src›.symm]
    by_cases he : i = extra
    · subst i; simp [S₃,S₂,‹extra ≠ src›,hextra]
    · simp [S₃,S₂,hi,he]

def generatedNarrowPackets (wide width src dst zero extra tmp : Fin T) : Pr P T Q A U :=
  withWidthDifference wide width extra tmp
    (topPass src dst (floorSliceWord src dst zero width extra tmp))

def generatedWidenPackets (wide width src dst extra tmp : Fin T) : Pr P T Q A U :=
  withWidthDifference wide width extra tmp
    (topPass src dst (topWidenWord src dst width extra tmp))

/-- Narrow from retained width headers; no difference counter is supplied. -/
theorem generatedNarrowPackets_exec {wide width src dst zero extra tmp : Fin T}
    (hreg : [wide,width,src,dst,zero,extra,tmp].Nodup)
    (W w : ℕ) (hW : 1 ≤ W) (hw : w ≤ W)
    (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A W xs)
    (hdst : S.R dst = []) (hzero : S.R zero = [])
    (hextra : S.R extra = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (generatedNarrowPackets wide width src dst zero extra tmp) (mk v S)
        (4*W+4*w+2*(W-w)+(xs.length*(4*W+2*w+14)+4)+10)
        (mk v' {S with R := Function.update S.R src (cstream A w xs)}) := by
  have hr := hreg
  regs_ne hr
  apply withWidthDifference_exec (body := body) (by regs_nodup)
    _ W w _ _ S hwide hwidth hextra htmp ?_ v
  intro v₀
  apply narrowPackets_exec (body := body) (by regs_nodup) W w hW hw xs v₀
  · simpa [‹src ≠ extra›] using hsrc
  · simpa [‹dst ≠ extra›] using hdst
  · simpa [‹zero ≠ extra›] using hzero
  · simpa [‹width ≠ extra›] using hwidth
  · simp
  · simpa [‹extra ≠ tmp›.symm] using htmp

/-- Widen numerical results and dispose the generated difference counter. -/
theorem generatedWidenPackets_exec {wide width src dst extra tmp : Fin T}
    (hreg : [wide,width,src,dst,extra,tmp].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (xs : List GaussianInt) (hfit : ∀ z ∈ xs, TopFitsZ w z)
    (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hextra : S.R extra = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (generatedWidenPackets wide width src dst extra tmp) (mk v S)
        (4*W+4*w+2*(W-w)+(xs.length*(6*W+10)+4)+10)
        (mk v' {S with R := Function.update S.R src (cstream A W xs)}) := by
  have hr := hreg
  regs_ne hr
  apply withWidthDifference_exec (body := body) (by regs_nodup)
    _ W w _ _ S hwide hword hextra htmp ?_ v
  intro v₀
  apply widenPackets_exec (body := body) (by regs_nodup) w W hw hwidth xs hfit v₀
  · simpa [‹src ≠ extra›] using hsrc
  · simpa [‹dst ≠ extra›] using hdst
  · exact ⟨by simpa [‹width ≠ extra›] using hword,by simp,
      by simpa [‹extra ≠ tmp›.symm] using htmp⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
