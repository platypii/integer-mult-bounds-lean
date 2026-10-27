module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSelectWord

/-! Consume one mask symbol and one input word, emitting that word or an encoded zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def maskedTransferWord (width mask src dst trash tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.pop (.rt mask) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
    (.cond (·.flag) (transfer width src dst tmp)
      (.seq (discardPrefix width src trash tmp)
        (copyR width dst tmp (fun _ => pairSym A false false))))

theorem maskedTransferWord_exec {width mask src dst trash tmp : Fin T}
    (hreg : [width,mask,src,dst,trash,tmp].Nodup) (hA : 4 ≤ A)
    (flag : Bool) (w : ℕ) (x : GaussianInt) (tail maskTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = pairSym A flag flag::maskTail)
    (hsrc : S.R src = csyms A w x++tail) (hw : (S.R width).length = w)
    (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10*w+12 ∧
      Exec body (maskedTransferWord width mask src dst trash tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          mask maskTail) src tail) dst ((csyms A w (if flag then x else 0)).reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  let S₀ : Stacks T A := {S with R := Function.update S.R mask maskTail}
  have hpop : Exec body (.act (.pop (.rt mask)
      (fun v o => {v with flag := pairRe (o.getD blank)}) .done)) (mk v S) 1
      (mk {v with flag := flag} S₀) := by
    simpa [S₀,Action.run,update_rt,hmask,pairRe_pairSym hA] using
      (Exec.act (body := body) (.pop (.rt mask)
        (fun v o => {v with flag := pairRe (o.getD blank)}) .done) (mk v S))
  cases flag
  · obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body)
      (count := width) (src := src) (trash := trash) (tmp := tmp) (by regs_nodup)
      (csyms A w x) tail {v with flag := false} S₀
      (by simpa [S₀,‹mask ≠ src›.symm] using hsrc)
      (by simpa [S₀,‹width ≠ mask›] using hw)
      (by simpa [S₀,‹mask ≠ trash›.symm] using htrash)
      (by simpa [S₀,‹mask ≠ tmp›.symm] using htmp)
    let S₁ : Stacks T A := {S₀ with R := Function.update S₀.R src tail}
    obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec body width dst tmp ‹width ≠ dst› ‹width ≠ tmp› ‹dst ≠ tmp›
      (fun _ => pairSym A false false) v₁ S₁
      (by simpa [S₁,S₀,‹src ≠ tmp›.symm,‹mask ≠ tmp›.symm] using htmp)
    refine ⟨v₂,1+((6*w+6)+(4*w+4)+1),hu₂.trans hu₁,by omega,
      (Exec.seq hpop (Exec.cond_false rfl (Exec.seq he₁ he₂))).cast ?_ ?_⟩
    · simp [S₁,S₀,‹width ≠ src›,‹width ≠ mask›,hw]
    · apply congrArg (mk v₂)
      simp [S₁,S₀,csyms_zero,‹width ≠ src›,‹width ≠ mask›,‹src ≠ dst›.symm,‹mask ≠ dst›.symm,hw]
  · obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
      (count := width) (src := src) (dst := dst) (tmp := tmp) (by regs_nodup)
      {v with flag := true} S₀ (csyms A w x) tail
      (by simpa [S₀,‹mask ≠ src›.symm] using hsrc)
      (by simpa [S₀,‹width ≠ mask›] using hw)
      (by simpa [S₀,‹mask ≠ tmp›.symm] using htmp)
    refine ⟨v₁,1+((4*w+4)+1),hu₁,by omega,
      (Exec.seq hpop (Exec.cond_true rfl he₁)).cast (by simp) ?_⟩
    simp [S₀,‹mask ≠ dst›.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
