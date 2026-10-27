module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Borrowed unary comparison with scratch released before either continuation runs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def unaryIfLt (a b work tmp : Fin T) (yes no : Pr P T Q A U) : Pr P T Q A U :=
  .seq (ucopy b work tmp) (.seq (usub a work tmp) (.seq (.act (peekR work))
    (.cond (·.flag) (.seq (uclear work) yes) (.seq (uclear work) no))))

def unaryIfLtCost (n m : ℕ) : ℕ := (4*m+4)+((4*n+4)+(1+(1+(2*(m-n)+2))))

theorem unaryIfLt_exec {a b work tmp : Fin T} (hreg : [a,b,work,tmp].Nodup)
    (yes no : Pr P T Q A U) (n m budget : ℕ) (S S' : Stacks T A)
    (hn : (S.R a).length = n) (hm : (S.R b).length = m) (hwork : S.R work = []) (htmp : S.R tmp = [])
    (hbranch : ∀ vi : HS T Q A U, ∃ v' steps, v'.user = vi.user ∧ steps ≤ budget ∧
      Exec body (if n < m then yes else no) (mk vi S) steps (mk v' S'))
    (v : HS T Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ unaryIfLtCost n m+budget ∧
      Exec body (unaryIfLt a b work tmp yes no) (mk v S) steps (mk v' S') := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := b) (b := work) (t := tmp)
    ‹b ≠ work› ‹b ≠ tmp› ‹work ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R work (List.replicate m tick)}
  have he₁' : Exec body (ucopy b work tmp) (mk v S) (4*m+4) (mk v₁ S₁) := by simpa [S₁,hm,hwork] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body (a := a) (b := work) (t := tmp)
    ‹a ≠ work› ‹a ≠ tmp› ‹work ≠ tmp› v₁ S₁ (by simpa [S₁,‹work ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S with R := Function.update S.R work (List.replicate (m-n) tick)}
  have he₂' : Exec body (usub a work tmp) (mk v₁ S₁) (4*n+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hn,‹a ≠ work›,List.drop_replicate] using he₂
  have hflag : (S₂.R work).head?.isSome = decide (n < m) := by
    by_cases h : n < m
    · have hne : m-n ≠ 0 := by omega
      simp [S₂,List.head?_replicate,hne,h]
    · have hz : m-n = 0 := by omega
      simp [S₂,hz,h]
  have he₃ := Exec.act (body := body) (peekR work) (mk v₂ S₂)
  rw [peekR_run,hflag] at he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body work {v₂ with flag := decide (n < m)} S₂
  have he₄' : Exec body (uclear work) (mk {v₂ with flag := decide (n < m)} S₂)
      (2*(m-n)+2) (mk v₄ S) := by
    convert he₄ using 1
    · simp [S₂]
    · apply congrArg (mk v₄)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = work <;> simp_all [S₂]
  obtain ⟨v₅,m₅,hu₅,hm₅,he₅⟩ := hbranch v₄
  have hcond : Exec body (.cond (·.flag) (.seq (uclear work) yes) (.seq (uclear work) no))
      (mk {v₂ with flag := decide (n < m)} S₂) (((2*(m-n)+2)+m₅)+1) (mk v₅ S') := by
    by_cases h : n < m
    · apply Exec.cond_true (by simp [h])
      simpa only [h,ite_true] using Exec.seq he₄' he₅
    · apply Exec.cond_false (by simp [h])
      simpa only [h,ite_false] using Exec.seq he₄' he₅
  refine ⟨v₅,(4*m+4)+((4*n+4)+(1+(((2*(m-n)+2)+m₅)+1))),
    hu₅.trans (hu₄.trans (hu₂.trans hu₁)),by dsimp [unaryIfLtCost]; omega,
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ hcond))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
