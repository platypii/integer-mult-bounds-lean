module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeaderWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire the owned ambient residual prefix, exposing the retained original RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def retireAmbientSource : Pr P₀ 144 Q A U :=
  .seq couplingHeaderWidth (.seq (unaryProduct 121 94 131 134 135)
    (.seq (discardPrefix 131 110 134 135) (clearWords [94,131])))

def retireAmbientSourceCost (q s : ℕ) : ℕ :=
  12*s*(2*q+8)+9*s+12*q+40

theorem retireAmbientSource_exec (q s : ℕ) (raw tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = raw++tail) (hlen : raw.length = s*(2*q+8))
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireAmbientSourceCost q s ∧
      Exec body retireAmbientSource (mk v S) m
        (mk v' {S with R := Function.update S.R 110 tail}) := by
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
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 134) (tmp := 135) (by decide)
    raw tail v₂ S₂ (by simpa [S₂,S₁] using hsrc) (by simp [S₂,hlen,w])
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 110 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(94 : Fin 144),131] (by decide) v₃ S₃
  have hsum : ([(94 : Fin 144),131].map (fun r => (S₃.R r).length)).sum = w+s*w := by
    simp [S₃,S₂,S₁]
  refine ⟨v₄,(8*q+9)+(m₂+((6*raw.length+6)+(2*(w+s*w)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hlen]
    dsimp only [retireAmbientSourceCost,w] at *
    nlinarith only [hm₂']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h94' : r = 94 <;> by_cases h131' : r = 131 <;>
      simp [S₃,S₂,S₁,h94',h131',h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
