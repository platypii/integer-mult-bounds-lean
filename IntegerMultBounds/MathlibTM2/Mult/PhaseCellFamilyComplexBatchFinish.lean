module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchLoop

/-! Restore borrowed complex inputs and publish solved replicas in their original order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

def familyComplexBatchFinish : Pr P 263 Q A U :=
  .seq (moveR 241 110 id) (.seq (moveR 242 132 id) (uclear 243))

theorem familyComplexBatchFinish_exec (v : HS 263 Q A U) (S : Stacks 263 A)
    (input output : List (Fin (A+4))) (hinput : S.R 241 = input.reverse)
    (houtput : S.R 242 = output.reverse) :
    ∃ v', v'.user = v.user ∧
      Exec body familyComplexBatchFinish (mk v S)
        (2*input.length+2*output.length+2*(S.R 243).length+6)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 110 (input++S.R 110)) 132 (output++S.R 132)) 241 []) 242 []) 243 [])}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body 241 110 (by decide) id v S
  let S₁ : Stacks 263 A := {S with R := movedR S.R 241 110 id (S.R 241)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 242 132 (by decide) id v₁ S₁
  let S₂ : Stacks 263 A := {S₁ with R := movedR S₁.R 242 132 id (S₁.R 242)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 243 v₂ S₂
  have hlen₁ : (S.R 241).length = input.length := by simp [hinput]
  have hlen₂ : (S₁.R 242).length = output.length := by simp [S₁,movedR,houtput]
  have hlen₃ : (S₂.R 243).length = (S.R 243).length := by simp [S₂,S₁,movedR]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  have hcost : 2*input.length+2*output.length+2*(S.R 243).length+6 =
      (2*(S.R 241).length+2)+((2*(S₁.R 242).length+2)+(2*(S₂.R 243).length+2)) := by
    rw [hlen₁,hlen₂,hlen₃]
    omega
  rw [hcost]
  exact he.cast rfl (congrArg (mk v₃) (by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h241 : i = 241 <;>
      by_cases h242 : i = 242 <;> by_cases h243 : i = 243 <;>
      simp [S₂,S₁,movedR,h110,h132,h241,h242,h243,hinput,houtput]))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
