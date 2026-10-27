module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalFinishComponentPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Pair two restored real solves and return the borrowed original input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def cleanFinishComponents : Pr P 224 Q A U :=
  .seq (generateWordWidth 119 94 135) (.seq (unaryProduct 121 94 131 134 135)
    (.seq (discardPrefix 131 110 136 134) (.seq physicalFinishComponentPair
      (.seq (movePrefix 131 146 110 147 134) (clearWords [94,131])))))

def cleanFinishComponentsCost (q s : ℕ) : ℕ := 34*s*(2*q+8)+9*s+12*q+60

theorem cleanFinishComponents_exec (hA : 4 ≤ A) (q s : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s)
    (rhs tail savedTail outputTail original originalTail : List (Fin (A+4)))
    (hrhs : rhs.length = s*(2*q+8)) (horiginal : original.length = s*(2*q+8))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 110 = rhs++tail) (hx : S.R 145 = cstream A (2*q+8) xs++savedTail)
    (hy : S.R 132 = cstream A (2*q+8) ys++outputTail) (horig : S.R 146 = original++originalTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h140 : S.R 140 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanFinishComponentsCost q s ∧
      Exec body cleanFinishComponents (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (original++tail)) 145 savedTail) 146 originalTail)
          132 (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  let w := 2*q+8
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 94) (tmp := 135) (by decide) q v S hq h94 h135
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₂' : Exec body (unaryProduct 121 94 131 134 135) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,h131] using he₂
  have hn₂' : n₂ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hn₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide) rhs tail v₂ S₂
    (by simpa [S₂,S₁] using hsource) (by simp [S₂,hrhs,w])
    (by simpa [S₂,S₁] using h136) (by simpa [S₂,S₁] using h134)
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 110 tail}
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := physicalFinishComponentPair_exec (body := body) hA s w xs ys hxlen hylen
    savedTail outputTail v₃ S₃ (by simp [S₃,S₂])
    (by simpa [S₃,S₂,S₁] using hx) (by simpa [S₃,S₂,S₁] using hy)
    (by simpa [S₃,S₂,S₁] using h134) (by simpa [S₃,S₂,S₁] using h140) (by simpa [S₃,S₂,S₁] using h147)
  let Z := cstream A w (List.zipWith pairComponentWord xs ys)++outputTail
  let S₄ : Stacks 224 A := {S₃ with R := Function.update (Function.update S₃.R 145 savedTail) 132 Z}
  obtain ⟨v₅,hu₅,he₅⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 146) (dst := 110) (saved := 147) (tmp := 134) (by decide)
    original originalTail v₄ S₄ (by simpa [S₄,S₃,S₂,S₁] using horig)
    (by simp [S₄,S₃,S₂,horiginal,w])
    (by simpa [S₄,S₃,S₂,S₁] using h147) (by simpa [S₄,S₃,S₂,S₁] using h134)
  let S₅ : Stacks 224 A := {S₄ with R := Function.update (Function.update S₄.R 146 originalTail) 110 (original++tail)}
  have he₅' : Exec body (movePrefix 131 146 110 147 134) (mk v₄ S₄) (6*original.length+6) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := body) ([94,131] : List (Fin 224)) (by decide) v₅ S₅
  have hsum : (([94,131] : List (Fin 224)).map fun i => (S₅.R i).length).sum = w+s*w := by
    simp [S₅,S₄,S₃,S₂,S₁]
  refine ⟨v₆,(8*q+9)+(n₂+((6*rhs.length+6)+(n₄+((6*original.length+6)+(2*(w+s*w)+5))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅' he₆))))).cast
      (by rw [hsum]; rfl) ?_⟩
  · dsimp only [cleanFinishComponentsCost]
    rw [hrhs,horiginal]
    dsimp only [w] at *
    nlinarith only [hn₂',hn₄]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h94' : i = 94 <;> by_cases h131' : i = 131 <;> by_cases h110 : i = 110 <;>
      by_cases h132 : i = 132 <;> by_cases h145 : i = 145 <;> by_cases h146 : i = 146 <;>
      simp [S₅,S₄,S₃,S₂,S₁,Z,w,h94',h131',h110,h132,h145,h146,h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
