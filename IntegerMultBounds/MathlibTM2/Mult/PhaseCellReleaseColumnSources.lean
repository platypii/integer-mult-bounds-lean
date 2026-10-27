module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingResult

/-! Release both owned column-source lines and publish the computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def releaseColumnSources : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 97 94 131 134 135) (.seq (discardPrefix 131 110 138 137)
    (.seq (discardPrefix 131 132 138 137) (.seq (uclear 131) feedCouplingResult)))

def releaseColumnSourcesCost (s w : ℕ) : ℕ := 30*s*w+18*s+30

theorem releaseColumnSources_exec (s w : ℕ)
    (rhs basis result tail sourceTail resultTail : List (Fin (A+4)))
    (hrhs : rhs.length = s*w) (hbasis : basis.length = s*w) (hresult : result.length = s*w)
    (v : HS 144 Q A U) (S : Stacks 144 A) (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (h110 : S.R 110 = rhs++tail) (h132 : S.R 132 = basis++sourceTail) (h113 : S.R 113 = result++resultTail)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h137 : S.R 137 = []) (h138 : S.R 138 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseColumnSourcesCost s w ∧
      Exec body releaseColumnSources (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          110 (result++tail)) 132 sourceTail) 113 resultTail)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 97 94 131 134 135) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa only [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 138) (tmp := 137) (by decide)
    rhs tail v₁ S₁ (by simpa [S₁] using h110) (by simp [S₁,hrhs])
    (by simpa [S₁] using h138) (by simpa [S₁] using h137)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 132) (trash := 138) (tmp := 137) (by decide)
    basis sourceTail v₂ S₂ (by simpa [S₂,S₁] using h132) (by simp [S₂,S₁,hbasis])
    (by simpa [S₂,S₁] using h138) (by simpa [S₂,S₁] using h137)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 132 sourceTail}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 131 v₃ S₃
  let S₄ : Stacks 144 A := {S₃ with R := Function.update S₃.R 131 []}
  obtain ⟨v₅,m₅,hu₅,hm₅,he₅⟩ := feedCouplingResult_exec (body := body) s w result resultTail v₄ S₄
    (by simpa [S₄,S₃,S₂,S₁] using hs) (by simpa [S₄,S₃,S₂,S₁] using hw)
    (by simpa [S₄,S₃,S₂,S₁] using h113) hresult (by simp [S₄])
    (by simpa [S₄,S₃,S₂,S₁] using h134) (by simpa [S₄,S₃,S₂,S₁] using h135)
  refine ⟨v₅,m₁+((6*rhs.length+6)+((6*basis.length+6)+((2*(s*w)+2)+m₅))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by simp [S₃,S₂,S₁]) ?_⟩
  · rw [hrhs,hbasis]
    dsimp [releaseColumnSourcesCost]
    nlinarith only [hm₁',hm₅]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110' : k = 110 <;> by_cases h132' : k = 132 <;> by_cases h113' : k = 113 <;>
      by_cases h131' : k = 131 <;> simp [S₄,S₃,S₂,S₁,h110',h132',h113',h131',h131]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
