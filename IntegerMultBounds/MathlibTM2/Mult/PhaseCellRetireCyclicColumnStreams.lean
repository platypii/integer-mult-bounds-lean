module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireResidentColumn

/-! Retire the original column and two residual streams with one shared byte clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def retireCyclicColumnStreams : Pr P 151 Q A U :=
  .seq residentColumnWidth (.seq (unaryProduct 121 94 131 134 135)
    (.seq (discardPrefix 131 132 138 134) (.seq (discardPrefix 131 132 138 134)
      (.seq (discardPrefix 131 110 138 134) (clearWords [94,131])))))

def retireCyclicColumnStreamsCost (q s : ℕ) : ℕ :=
  let w := 2*q+8
  (8*q+9)+(s*(4*w+9)+4+((6*s*w+6)+((6*s*w+6)+((6*s*w+6)+(2*(w+s*w)+5)))))

theorem retireCyclicColumnStreams_exec (q s : ℕ)
    (right left original outputTail inputTail : List (Fin (A+4)))
    (hR : right.length = s*(2*q+8)) (hL : left.length = s*(2*q+8)) (hB : original.length = s*(2*q+8))
    (v : HS 151 Q A U) (S : Stacks 151 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 132 = right++(left++outputTail)) (hinput : S.R 110 = original++inputTail)
    (hfresh : ∀ k ∈ [(94 : Fin 151),131,134,135,138], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireCyclicColumnStreamsCost q s ∧
      Exec body retireCyclicColumnStreams (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 132 outputTail) 110 inputTail}) := by
  let w := 2*q+8
  obtain ⟨v₁,hv₁,he₁⟩ := residentColumnWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₂' : Exec body (unaryProduct 121 94 131 134 135) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,hfresh 131 (by simp)] using he₂
  have hm₂' : m₂ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hm₂
  obtain ⟨v₃,hv₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 132) (trash := 138) (tmp := 134) (by decide)
    right (left++outputTail) v₂ S₂ (by simpa [S₂,S₁] using hsrc) (by simp [S₂,hR,w])
    (by simpa [S₂,S₁] using hfresh 138 (by simp)) (by simpa [S₂,S₁] using hfresh 134 (by simp))
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 132 (left++outputTail)}
  obtain ⟨v₄,hv₄,he₄⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 132) (trash := 138) (tmp := 134) (by decide)
    left outputTail v₃ S₃ (by simp [S₃]) (by simp [S₃,S₂,hL,w])
    (by simpa [S₃,S₂,S₁] using hfresh 138 (by simp)) (by simpa [S₃,S₂,S₁] using hfresh 134 (by simp))
  let S₄ : Stacks 151 A := {S₃ with R := Function.update S₃.R 132 outputTail}
  obtain ⟨v₅,hv₅,he₅⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 138) (tmp := 134) (by decide)
    original inputTail v₄ S₄ (by simpa [S₄,S₃,S₂,S₁] using hinput) (by simp [S₄,S₃,S₂,hB,w])
    (by simpa [S₄,S₃,S₂,S₁] using hfresh 138 (by simp)) (by simpa [S₄,S₃,S₂,S₁] using hfresh 134 (by simp))
  let S₅ : Stacks 151 A := {S₄ with R := Function.update S₄.R 110 inputTail}
  obtain ⟨v₆,hv₆,he₆⟩ := clearWords_exec (body := body) [(94 : Fin 151),131] (by decide) v₅ S₅
  have hsum : ([(94 : Fin 151),131].map (fun k => (S₅.R k).length)).sum = w+s*w := by simp [S₅,S₄,S₃,S₂,S₁]
  refine ⟨v₆,(8*q+9)+(m₂+((6*right.length+6)+((6*left.length+6)+((6*original.length+6)+(2*(w+s*w)+5))))),
    hv₆.trans (hv₅.trans (hv₄.trans (hv₃.trans (hv₂.trans hv₁)))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hR,hL,hB]
    dsimp [retireCyclicColumnStreamsCost,w] at *
    nlinarith only [hm₂']
  · apply congrArg (mk v₆)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      by_cases h131 : k = 131
      · subst k; simp [hfresh 131 (by simp)]
      simp [S₅,S₄,S₃,S₂,S₁,h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
