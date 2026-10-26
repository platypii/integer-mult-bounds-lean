module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Reverse an owned coefficient prefix without changing its borrowed suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def reversePrefixInPlace (records recordSaved width src dst saved buf tmp count : Fin T) : Pr P₀ T Q A U :=
  .seq (reverseWords records recordSaved width src dst saved buf tmp)
    (.seq (unaryProduct records width count recordSaved saved)
      (.seq (discardPrefix count src buf saved)
        (.seq (uclear count) (.seq (moveR dst buf id) (moveR buf src id)))))

theorem reversePrefixInPlace_exec {records recordSaved width src dst saved buf tmp count : Fin T}
    (hreg : [records,recordSaved,width,src,dst,saved,buf,tmp,count].Nodup)
    (w : ℕ) (xs : List GaussianInt) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrecords : (S.R records).length = xs.length) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hfresh : ∀ r ∈ [recordSaved,dst,saved,buf,tmp,count], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 32*xs.length*w+28*xs.length+22 ∧
      Exec body (reversePrefixInPlace records recordSaved width src dst saved buf tmp count) (mk v S) m
        (mk v' {S with R := Function.update S.R src (cstream A w xs.reverse++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := reverseWords_coeffs_exec (body := body)
    (records := records) (recordSaved := recordSaved) (width := width) (src := src)
    (dst := dst) (saved := saved) (buf := buf) (tmp := tmp) (by regs_nodup) w xs v S tail
    hrecords hsrc hwidth (hfresh recordSaved (by simp)) (hfresh saved (by simp))
    (hfresh buf (by simp)) (hfresh tmp (by simp))
  let ys := cstream A w xs.reverse
  let S₁ : Stacks T A := {S with R := Function.update S.R dst ys}
  have he₁' : Exec body (reverseWords records recordSaved width src dst saved buf tmp) (mk v S)
      (xs.length*(16*w+19)+6) (mk v₁ S₁) := by simpa [S₁,ys,hfresh dst (by simp)] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := records) (b := width) (dst := count) (t₁ := recordSaved) (t₂ := saved) (by regs_nodup) v₁ S₁
    (by simpa [S₁,‹recordSaved ≠ dst›] using hfresh recordSaved (by simp))
    (by simpa [S₁,‹dst ≠ saved›.symm] using hfresh saved (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count (List.replicate (xs.length*w) tick)}
  have he₂' : Exec body (unaryProduct records width count recordSaved saved) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,‹records ≠ dst›,‹width ≠ dst›,‹dst ≠ count›.symm,hrecords,hwidth,hfresh count (by simp)] using he₂
  have hm₂' : m₂ ≤ xs.length*(4*w+9)+4 := by
    simpa [S₁,‹records ≠ dst›,‹width ≠ dst›,hrecords,hwidth] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := count) (src := src) (trash := buf) (tmp := saved) (by regs_nodup)
    (cstream A w xs) tail v₂ S₂
    (by simpa [S₂,S₁,‹src ≠ count›,‹src ≠ dst›] using hsrc)
    (by simp [S₂])
    (by simpa [S₂,S₁,‹buf ≠ count›,‹dst ≠ buf›.symm] using hfresh buf (by simp))
    (by simpa [S₂,S₁,‹saved ≠ count›,‹dst ≠ saved›.symm] using hfresh saved (by simp))
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R src tail}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) count v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R count []}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body dst buf ‹dst ≠ buf› id v₄ S₄
  let S₅ : Stacks T A := {S₄ with R := movedR S₄.R dst buf id (S₄.R dst)}
  obtain ⟨v₆,hu₆,he₆⟩ := moveR_exec body buf src ‹src ≠ buf›.symm id v₅ S₅
  have hdst : S₄.R dst = ys := by simp [S₄,S₃,S₂,S₁,‹dst ≠ count›,‹src ≠ dst›.symm]
  have hbuf : S₄.R buf = [] := by
    simpa [S₄,S₃,S₂,S₁,‹buf ≠ count›,‹src ≠ buf›.symm,‹dst ≠ buf›.symm] using hfresh buf (by simp)
  have hbuf₅ : S₅.R buf = ys.reverse := by simp [S₅,movedR,hdst,hbuf]
  have hsrc₅ : S₅.R src = tail := by
    simp [S₅,movedR,S₄,S₃,‹src ≠ buf›,‹src ≠ dst›,‹src ≠ count›]
  refine ⟨v₆,(xs.length*(16*w+19)+6)+(m₂+((6*(xs.length*w)+6)+
    ((2*(xs.length*w)+2)+((2*(xs.length*w)+2)+(2*(xs.length*w)+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · nlinarith only [hm₂']
  · simp [S₃,S₂,‹src ≠ count›.symm,hdst,hbuf₅,ys]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases hc : r = count
    · subst r
      simp [S₅,S₄,S₃,S₂,S₁,movedR,Function.update_apply,‹dst ≠ count›.symm,‹buf ≠ count›.symm,
        ‹src ≠ count›.symm,hfresh count (by simp)]
    by_cases hd : r = dst
    · subst r
      simp [S₅,S₄,S₃,S₂,S₁,movedR,Function.update_apply,‹src ≠ dst›.symm,‹dst ≠ buf›,
        hfresh dst (by simp)]
    by_cases hb : r = buf
    · subst r
      simp [S₅,S₄,S₃,S₂,S₁,movedR,Function.update_apply,‹src ≠ buf›.symm,hfresh buf (by simp)]
    by_cases hs : r = src
    · subst r
      simp [movedR,hbuf₅,hsrc₅,ys]
    simp [S₅,S₄,S₃,S₂,S₁,movedR,Function.update_apply,hc,hd,hb,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
