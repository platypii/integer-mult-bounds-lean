module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Reset the per-input word-width header after coefficient-page disposal. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def resetPackedInputWidth : Pr P 248 Q A U := clearWords [130]

theorem resetPackedInputWidth_exec (w : ℕ) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hwidth : (S.R 130).length = w) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2*w+3 ∧
      Exec body resetPackedInputWidth (mk v S) n
        (mk v' {S with R := Function.update S.R 130 []}) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(130 : Fin 248)] (by decide) v S
  refine ⟨v',_,hu,?_,he.cast rfl ?_⟩
  · simp [hwidth]
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 130 <;> simp [hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
