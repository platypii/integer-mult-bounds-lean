module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeMarkedWidth

/-! Publish a width prefix and release the width register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishMarkedWidth (width dst tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => bitSymbol false) .done))
    (.seq (ucopy width dst tmp) (uclear width))

theorem publishMarkedWidth_exec (width dst tmp : Fin T)
    (hreg : [width,dst,tmp].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (publishMarkedWidth width dst tmp) (mk v S) (6*(S.R width).length+7)
        (mk v' {S with R := (Function.update (Function.update S.R dst
          (List.replicate (S.R width).length tick++bitSymbol false::S.R dst)) width [])}) := by
  have : width ≠ dst := by intro h; subst dst; simp at hreg
  have : width ≠ tmp := by intro h; subst tmp; simp at hreg
  have : dst ≠ tmp := by intro h; subst tmp; simp at hreg
  let S₁ : Stacks T A := {S with R := Function.update S.R dst (bitSymbol false::S.R dst)}
  have he₁ : Exec body (.act (.push (.rt dst) (fun _ => bitSymbol false) .done))
      (mk v S) 1 (mk v S₁) := by
    simpa [Action.run,update_rt,S₁] using
      Exec.act (body := body) (.push (.rt dst) (fun _ => bitSymbol false) .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body ‹width ≠ dst› ‹width ≠ tmp› ‹dst ≠ tmp› v S₁
    (by simpa [S₁,‹dst ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R dst
    (List.replicate (S₁.R width).length tick++S₁.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) width v₂ S₂
  refine ⟨v₃,hu₃.trans hu₂,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁,‹width ≠ dst›]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases hw : r = width <;> by_cases hd : r = dst <;> simp_all [S₂,S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
