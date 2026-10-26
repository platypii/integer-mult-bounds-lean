module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyIndexedWord

/-! Consume a unary mask bit and gather either the indexed word or an encoded zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def maskedIndexedWord (mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T) : Pr P₀ T Q A U :=
  .seq (.act (peekR mask)) (.seq
    (.cond (·.flag) (copyIndexedWord index width src dst skip savedSkip saved tmp work₁ work₂)
      (copyR width dst saved (fun _ => pairSym A false false))) (uclear mask))

theorem maskedIndexedWord_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (flag : Bool) (w j : ℕ) (xs : List GaussianInt) (hj : j < xs.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = if flag then [tick] else [])
    (hindex : (S.R index).length = j) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+28 ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R dst
          (csyms A w (if flag then xs[j] else 0)++S.R dst)) mask []}) := by
  have hr := hreg
  regs_ne hr
  let z := if flag then xs[j] else 0
  let p : Pr P₀ T Q A U := copyIndexedWord index width src dst skip savedSkip saved tmp work₁ work₂
  let zero : Pr P₀ T Q A U := copyR width dst saved (fun _ => pairSym A false false)
  have hflag : (S.R mask).head?.isSome = flag := by cases flag <;> simp [hmask]
  have hpeek := Exec.act (body := body) (peekR mask) (mk v S)
  rw [peekR_run,hflag] at hpeek
  have hcopy : ∃ v₁ m₁, v₁.user = v.user ∧ m₁ ≤ j*(12*w+9)+10*w+23 ∧
      Exec body (.cond (·.flag) p zero) (mk {v with flag := flag} S) m₁
        (mk v₁ {S with R := Function.update S.R dst (csyms A w z++S.R dst)}) := by
    cases flag
    · obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body width dst saved ‹width ≠ dst› ‹width ≠ saved› ‹dst ≠ saved›
        (fun _ => pairSym A false false) {v with flag := false} S (hfresh saved (by simp))
      refine ⟨v₁,4*w+5,hu₁,by omega,?_⟩
      apply Exec.cond_false rfl
      simpa [z,zero,hwidth,csyms_zero] using he₁
    · obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := copyIndexedWord_exec (body := body)
        (index := index) (width := width) (src := src) (dst := dst) (skip := skip)
        (savedSkip := savedSkip) (saved := saved) (tmp := tmp) (work₁ := work₁) (work₂ := work₂)
        (by regs_nodup) w j xs hj tail {v with flag := true} S hindex hwidth hsrc hfresh
      exact ⟨v₁,m₁+1,hu₁,by omega,Exec.cond_true rfl he₁⟩
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := hcopy
  let S₁ : Stacks T A := {S with R := Function.update S.R dst (csyms A w z++S.R dst)}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body mask v₁ S₁
  have hlen : (S₁.R mask).length ≤ 1 := by cases flag <;> simp [S₁,‹mask ≠ dst›,hmask]
  refine ⟨v₂,1+(m₁+(2*(S₁.R mask).length+2)),hu₂.trans hu₁,by omega,
    Exec.seq hpeek (Exec.seq he₁ he₂)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
