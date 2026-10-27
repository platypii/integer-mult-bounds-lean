module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginalPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Retire the owned original column below its computed Schur column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def releaseSchurColumnInput : Pr P₀ 148 Q A U :=
  .seq originalInputClock (.seq (movePrefix 131 110 137 147 134)
    (.seq (discardPrefix 131 110 138 134)
      (.seq (movePrefix 131 137 110 147 134) (clearWords [94,131]))))

def releaseSchurColumnInputCost (q s : ℕ) : ℕ := 24*s*(2*q+8)+9*s+12*q+52

theorem releaseSchurColumnInput_exec (q s : ℕ) (xs ys tail : List (Fin (A+4)))
    (hx : xs.length = s*(2*q+8)) (hy : ys.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A) (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 110 = xs++(ys++tail))
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h137 : S.R 137 = []) (h138 : S.R 138 = []) (h147 : S.R 147 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseSchurColumnInputCost q s ∧
      Exec (embTab componentReg body) releaseSchurColumnInput (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (xs++tail)}) := by
  let w := 2*q+8
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := originalInputClock_exec (body := body) q s v S hq hs h94 h131 h134 h135
  let S₁ : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 94 (List.replicate w tick)) 131 (List.replicate (s*w) tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := movePrefix_exec (body := embTab componentReg body)
    (count := 131) (src := 110) (dst := 137) (saved := 147) (tmp := 134) (by decide)
    xs (ys++tail) v₁ S₁ (by simpa [S₁] using hsource) (by simp [S₁,hx,w])
    (by simpa [S₁] using h147) (by simpa [S₁] using h134)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 110 (ys++tail)) 137 xs}
  have he₂' : Exec (embTab componentReg body) (movePrefix 131 110 137 147 134)
      (mk v₁ S₁) (6*xs.length+6) (mk v₂ S₂) := by simpa [S₂,S₁,h137] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := embTab componentReg body)
    (count := 131) (src := 110) (trash := 138) (tmp := 134) (by decide)
    ys tail v₂ S₂ (by simp [S₂]) (by simp [S₂,S₁,hy,w])
    (by simpa [S₂,S₁] using h138) (by simpa [S₂,S₁] using h134)
  let S₃ : Stacks 148 A := {S₂ with R := Function.update S₂.R 110 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := movePrefix_exec (body := embTab componentReg body)
    (count := 131) (src := 137) (dst := 110) (saved := 147) (tmp := 134) (by decide)
    xs [] v₃ S₃ (by simp [S₃,S₂]) (by simp [S₃,S₂,S₁,hx,w])
    (by simpa [S₃,S₂,S₁] using h147) (by simpa [S₃,S₂,S₁] using h134)
  let S₄ : Stacks 148 A := {S₃ with R := Function.update (Function.update S₃.R 137 []) 110 (xs++tail)}
  have he₄' : Exec (embTab componentReg body) (movePrefix 131 137 110 147 134)
      (mk v₃ S₃) (6*xs.length+6) (mk v₄ S₄) := by simpa [S₄,S₃] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := embTab componentReg body) [(94 : Fin 148),131] (by decide) v₄ S₄
  have hsum : ([(94 : Fin 148),131].map (fun r => (S₄.R r).length)).sum = w+s*w := by simp [S₄,S₃,S₂,S₁]
  refine ⟨v₅,m₁+((6*xs.length+6)+((6*ys.length+6)+((6*xs.length+6)+(2*(w+s*w)+5)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅)))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hx,hy]
    change _ ≤ 24*s*w+9*s+12*q+52
    change m₁ ≤ 8*q+9+(s*(4*w+9)+4) at hm₁
    dsimp [w] at *
    nlinarith only [hm₁]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      by_cases h137' : k = 137 <;> by_cases h110 : k = 110 <;>
      simp [S₄,S₃,S₂,S₁,h94',h131',h137',h110,h94,h131,h137,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
