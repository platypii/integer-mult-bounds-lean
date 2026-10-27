module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Move one owned lookup word into the accumulated factor input, restoring both borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def feedFactorWord : Pr P 154 Q A U :=
  .seq (generateWordWidth 119 131 135) (.seq (movePrefix 131 143 140 134 136) (uclear 131))

def feedFactorWordCost (q : ℕ) : ℕ := (8*q+9)+((6*(2*q+8)+6)+(2*(2*q+8)+2))

theorem feedFactorWord_exec (q : ℕ) (z : GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 154 Q A U) (S : Stacks 154 A) (hq : (S.R 119).length = q)
    (hsrc : S.R 143 = csyms A (2*q+8) z++tail)
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body feedFactorWord (mk v S) (feedFactorWordCost q)
      (mk v' {S with R := (Function.update (Function.update S.R 143 tail) 140
        (csyms A (2*q+8) z++S.R 140))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 131) (tmp := 135) (by decide) q v S hq
    (hfresh 131 (by simp)) (hfresh 135 (by simp))
  let w := 2*q+8
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 131 (List.replicate w tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 143) (dst := 140) (saved := 134) (tmp := 136) (by decide)
    (csyms A w z) tail v₁ S₁ (by simpa [S₁] using hsrc) (by simp [S₁])
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 136 (by simp))
  let output := csyms A w z++S.R 140
  let S₂ : Stacks 154 A := {S₁ with R := Function.update (Function.update S₁.R 143 tail) 140 output}
  have he₂' : Exec body (movePrefix 131 143 140 134 136) (mk v₁ S₁) (6*w+6) (mk v₂ S₂) := by
    simpa [S₂,S₁,output] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 131 v₂ S₂
  have hlen : (S₂.R 131).length = w := by simp [S₂,S₁]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk131 : k = 131 <;> by_cases hk140 : k = 140 <;> by_cases hk143 : k = 143 <;>
    simp [S₂,S₁,output,w,hk131,hk140,hk143,hfresh 131 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
