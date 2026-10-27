module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Switch between two real solves after the first solver has restored its workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def cleanComponentTransition : Pr P 224 Q A U :=
  .seq (generateWordWidth 119 94 135) (.seq (unaryProduct 121 94 131 134 135)
    (.seq (.seq (discardPrefix 131 110 136 134)
      (.seq (movePrefix 131 132 145 147 134) (movePrefix 131 144 110 147 134))) (clearWords [94,131])))

def cleanComponentTransitionCost (q s : ℕ) : ℕ := 24*s*(2*q+8)+9*s+12*q+52

theorem cleanComponentTransition_exec (q s : ℕ) (rhs result next tail outputTail parkedTail : List (Fin (A+4)))
    (hb : rhs.length = s*(2*q+8))
    (hout : result.length = s*(2*q+8)) (hnext : next.length = s*(2*q+8))
    (v : HS 224 Q A U) (S : Stacks 224 A) (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = rhs++tail) (hresult : S.R 132 = result++outputTail)
    (hparked : S.R 144 = next++parkedTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanComponentTransitionCost q s ∧
      Exec body cleanComponentTransition (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) := by
  let w := 2*q+8
  obtain ⟨v₂,hu₂,he₂'⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 94) (tmp := 135) (by decide) q v S hq h94 h135
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₂ S₁
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₃' : Exec body (unaryProduct 121 94 131 134 135)
      (mk v₂ S₁) n₃ (mk v₃ S₂) := by simpa [S₂,S₁,hs,h131] using he₃
  have hn₃' : n₃ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hn₃
  obtain ⟨va,hua,hea⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide) rhs tail v₃ S₂
    (by simpa [S₂,S₁] using hsrc) (by simp [S₂,hb,w])
    (by simpa [S₂,S₁] using h136) (by simpa [S₂,S₁] using h134)
  let Sa : Stacks 224 A := {S₂ with R := Function.update S₂.R 110 tail}
  obtain ⟨vb,hub,heb⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 132) (dst := 145) (saved := 147) (tmp := 134) (by decide)
    result outputTail va Sa (by simpa [Sa,S₂,S₁] using hresult) (by simp [Sa,S₂,hout,w])
    (by simpa [Sa,S₂,S₁] using h147) (by simpa [Sa,S₂,S₁] using h134)
  let Sb : Stacks 224 A := {Sa with R := Function.update (Function.update Sa.R 132 outputTail) 145 (result++Sa.R 145)}
  obtain ⟨v₄,huc,hec⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 144) (dst := 110) (saved := 147) (tmp := 134) (by decide)
    next parkedTail vb Sb (by simpa [Sb,Sa,S₂,S₁] using hparked) (by simp [Sb,Sa,S₂,hnext,w])
    (by simpa [Sb,Sa,S₂,S₁] using h147) (by simpa [Sb,Sa,S₂,S₁] using h134)
  have he₄ : Exec body
      (.seq (discardPrefix 131 110 136 134) (.seq (movePrefix 131 132 145 147 134) (movePrefix 131 144 110 147 134)))
      (mk v₃ S₂) (18*(s*w)+18)
      (mk v₄ {S₂ with R := (Function.update (Function.update (Function.update (Function.update S₂.R
        110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S₂.R 145))}) := by
    refine (Exec.seq hea (Exec.seq heb hec)).cast (by rw [hb,hout,hnext]; dsimp only [w]; ring) ?_
    apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h144 : i = 144 <;> by_cases h145 : i = 145 <;>
      simp [Sb,Sa,h110,h132,h144,h145]
  have hu₄ := huc.trans (hub.trans hua)
  let S₃ : Stacks 224 A := {S₂ with R := (Function.update (Function.update (Function.update (Function.update S₂.R
    110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S₂.R 145))}
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := body) [(94 : Fin 224),131] (by decide) v₄ S₃
  have hsum : ([(94 : Fin 224),131].map (fun r => (S₃.R r).length)).sum = w+s*w := by simp [S₃,S₂,S₁]
  refine ⟨v₅,(8*q+9)+(n₃+((18*(s*w)+18)+(2*(w+s*w)+5))),
    hu₅.trans (hu₄.trans (hu₃.trans hu₂)),?_,
    (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [cleanComponentTransitionCost,w] at *
    nlinarith only [hn₃']
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      simp [S₃,S₂,S₁,h94',h131',h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
