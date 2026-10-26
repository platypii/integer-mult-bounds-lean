module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput

/-! Clear unused imaginary components of the owned interior and residual prefixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def realResidualProjection : Pr P₀ 144 Q A U :=
  .seq couplingHeaderWidth (.seq (unaryProduct 121 94 131 134 135)
    (.seq (realPrefix 131 132 134 135)
      (.seq (realPrefix 131 110 134 135) (clearWords [94,131]))))

def realResidualProjectionCost (q s : ℕ) : ℕ := 18*s*(2*q+8)+9*s+12*q+46

theorem realResidualProjection_exec (hA : 4 ≤ A) (q s : ℕ)
    (D R : List GaussianInt) (interiorTail rhsTail : List (Fin (A+4)))
    (hDlen : D.length = s) (hRlen : R.length = s)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hD : S.R 132 = cstream A (2*q+8) D++interiorTail)
    (hR : S.R 110 = cstream A (2*q+8) R++rhsTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ realResidualProjectionCost q s ∧
      Exec body realResidualProjection (mk v S) m
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A (2*q+8) (D.map realPartWord)++interiorTail))
          110 (cstream A (2*q+8) (R.map realPartWord)++rhsTail))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := couplingHeaderWidth_exec (body := body) q v S hq h94 h135
  let w := 2*q+8
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₂' : Exec body (unaryProduct 121 94 131 134 135) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,h131] using he₂
  have hm₂' : m₂ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := realPrefix_exec (body := body)
    (count := 131) (src := 132) (saved := 134) (tmp := 135) (by decide) v₂ S₂
    (cstream A w D) interiorTail (by simpa [S₂,S₁,w] using hD)
    (by simp [S₂,hDlen]) (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
  let S₃ : Stacks 144 A := {S₂ with R := (Function.update S₂.R 132
    ((cstream A w D).map realPartSymbol++interiorTail))}
  obtain ⟨v₄,hu₄,he₄⟩ := realPrefix_exec (body := body)
    (count := 131) (src := 110) (saved := 134) (tmp := 135) (by decide) v₃ S₃
    (cstream A w R) rhsTail (by simpa [S₃,S₂,S₁,w] using hR)
    (by simp [S₃,S₂,hRlen]) (by simpa [S₃,S₂,S₁] using h134) (by simpa [S₃,S₂,S₁] using h135)
  let S₄ : Stacks 144 A := {S₃ with R := (Function.update S₃.R 110
    ((cstream A w R).map realPartSymbol++rhsTail))}
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := body) [(94 : Fin 144),131] (by decide) v₄ S₄
  have hsum : ([(94 : Fin 144),131].map (fun r => (S₄.R r).length)).sum = w+s*w := by
    simp [S₄,S₃,S₂,S₁]
  refine ⟨v₅,(8*q+9)+(m₂+((6*(s*w)+6)+((6*(s*w)+6)+(2*(w+s*w)+5)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · dsimp only [realResidualProjectionCost,w] at *
    nlinarith only [hm₂']
  · rw [hsum]
    simp [hDlen,hRlen]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk94 : k = 94 <;> by_cases hk131 : k = 131 <;>
      simp [S₄,S₃,S₂,S₁,hk94,hk131,h94,h131,Function.update_apply,
        realPartSymbol_cstream hA,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
