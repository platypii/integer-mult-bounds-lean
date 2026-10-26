module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Park the inactive input in an outer register, restoring the real solver's input port. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def parkComponent : Pr P₀ 148 Q A U := .seq (moveR 137 147 id) (moveR 147 144 id)

theorem parkComponent_exec (v : HS 148 Q A U) (S : Stacks 148 A) (h147 : S.R 147 = []) :
    ∃ v', v'.user = v.user ∧ Exec body parkComponent (mk v S) (4*(S.R 137).length+4)
      (mk v' {S with R := (Function.update (Function.update S.R 137 []) 144 (S.R 137++S.R 144))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body 137 147 (by decide) id v S
  let S₁ : Stacks 148 A := {S with R := movedR S.R 137 147 id (S.R 137)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 147 144 (by decide) id v₁ S₁
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [S₁,movedR,h147]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h137 : k = 137 <;> by_cases h144 : k = 144 <;> by_cases h147' : k = 147 <;>
      simp [S₁,movedR,h137,h144,h147',h147]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
