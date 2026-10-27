module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentColumnWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire one owned ambient column and restore the borrowed source suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def retireResidentColumn : Pr P 151 Q A U :=
  .seq residentColumnWidth (.seq (unaryProduct 121 94 131 134 135)
    (.seq (discardPrefix 131 110 138 134) (clearWords [94,131])))

def retireResidentColumnCost (q s : ℕ) : ℕ :=
  let w := 2*q+8
  (8*q+9)+(s*(4*w+9)+4+((6*s*w+6)+(2*(w+s*w)+5)))

theorem retireResidentColumn_exec (q s : ℕ) (xs tail : List (Fin (A+4)))
    (hlen : xs.length = s*(2*q+8)) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = xs++tail)
    (hfresh : ∀ k ∈ [(94 : Fin 151),131,134,135,138], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireResidentColumnCost q s ∧
      Exec body retireResidentColumn (mk v S) m
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  let w := 2*q+8
  obtain ⟨v₁,hu₁,he₁⟩ := residentColumnWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₁ S₁
    (by simpa [S₁] using hfresh 134 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₂' : Exec body (unaryProduct 121 94 131 134 135) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,hfresh 131 (by simp)] using he₂
  have hm₂' : m₂ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 138) (tmp := 134) (by decide) xs tail v₂ S₂
    (by simpa [S₂,S₁] using hsrc) (by simp [S₂,hlen,w])
    (by simpa [S₂,S₁] using hfresh 138 (by simp)) (by simpa [S₂,S₁] using hfresh 134 (by simp))
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 110 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(94 : Fin 151),131] (by decide) v₃ S₃
  have hsum : ([(94 : Fin 151),131].map (fun k => (S₃.R k).length)).sum = w+s*w := by simp [S₃,S₂,S₁]
  refine ⟨v₄,(8*q+9)+(m₂+((6*xs.length+6)+(2*(w+s*w)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hlen]
    dsimp [retireResidentColumnCost,w] at *
    nlinarith only [hm₂']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk94 : k = 94 <;> by_cases hk131 : k = 131 <;> by_cases hk110 : k = 110 <;>
      simp [S₃,S₂,S₁,hk94,hk131,hk110,hfresh 94 (by simp),hfresh 131 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
