module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitComponents
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate and retire the byte count for splitting the original complex RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def splitComponentLine : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 121 94 131 134 135)
    (.seq (splitComponentPrefix 131 110 137 136 134) (uclear 131))

def splitComponentLineCost (s w : ℕ) : ℕ := 16*s*w+9*s+16

theorem splitComponentLine_exec (hA : 4 ≤ A) (s w : ℕ) (zs : List GaussianInt)
    (hzlen : zs.length = s) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w zs++tail)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h136 : S.R 136 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ splitComponentLineCost s w ∧
      Exec body splitComponentLine (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R
          110 (cstream A w (zs.map realPartWord)++tail))
          137 (cstream A w (zs.map imagPartWord)++S.R 137))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 94 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := splitComponentPrefix_exec (body := body)
    (count := 131) (src := 110) (dst := 137) (saved := 136) (tmp := 134) (by decide)
    hA w zs tail v₁ S₁ (by simpa [S₁] using hsrc) (by simp [S₁,hzlen])
    (by simpa [S₁] using h136) (by simpa [S₁] using h134)
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R
    110 (cstream A w (zs.map realPartWord)++tail)) 137 (cstream A w (zs.map imagPartWord)++S₁.R 137))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 131 v₂ S₂
  refine ⟨v₃,n₁+((10*zs.length*w+10)+(2*(s*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hzlen]
    dsimp [splitComponentLineCost]
    nlinarith only [hn₁']
  · simp [S₂,S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h1 : k = 131 <;> by_cases h2 : k = 110 <;> by_cases h3 : k = 137 <;>
      simp [S₂,S₁,h1,h2,h3,h131]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
