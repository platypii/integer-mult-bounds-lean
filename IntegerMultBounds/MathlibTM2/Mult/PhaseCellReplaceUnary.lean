module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Replace an owned unary dimension from a retained source, restoring scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replaceUnary (src dst tmp : Fin T) : Pr P T Q A U := .seq (uclear dst) (ucopy src dst tmp)

theorem replaceUnary_exec {src dst tmp : Fin T} (hreg : [src,dst,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (replaceUnary src dst tmp) (mk v S)
        (2*(S.R dst).length+4*(S.R src).length+6)
        (mk v' {S with R := Function.update S.R dst (List.replicate (S.R src).length tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec body dst v S
  let S₁ : Stacks T A := {S with R := Function.update S.R dst []}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := src) (b := dst) (t := tmp)
    ‹src ≠ dst› ‹src ≠ tmp› ‹dst ≠ tmp› v₁ S₁ (by simpa [S₁,‹dst ≠ tmp›.symm] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp only [S₁,Function.update_of_ne ‹src ≠ dst›]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = dst <;> simp [S₁,hk,‹src ≠ dst›]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
