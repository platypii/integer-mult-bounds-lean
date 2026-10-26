module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Retire the first solve's two RHS pages, save its output and install the second input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def componentTransitionCore : Pr P₀ 148 Q A U :=
  .seq (discardPrefix 131 110 136 134) (.seq (discardPrefix 131 110 136 134)
    (.seq (movePrefix 131 132 145 147 134) (movePrefix 131 144 110 147 134)))

theorem componentTransitionCore_exec (n : ℕ) (recovery rhs result next tail outputTail parkedTail : List (Fin (A+4)))
    (hr : recovery.length = n) (hb : rhs.length = n) (hout : result.length = n) (hnext : next.length = n)
    (v : HS 148 Q A U) (S : Stacks 148 A) (hcount : (S.R 131).length = n)
    (hsrc : S.R 110 = recovery++(rhs++tail)) (hresult : S.R 132 = result++outputTail)
    (hparked : S.R 144 = next++parkedTail) (h134 : S.R 134 = []) (h136 : S.R 136 = []) (h147 : S.R 147 = []) :
    ∃ v', v'.user = v.user ∧ Exec body componentTransitionCore (mk v S) (24*n+24)
      (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide)
    recovery (rhs++tail) v S hsrc (by omega) h136 h134
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 110 (rhs++tail)}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide)
    rhs tail v₁ S₁ (by simp [S₁]) (by simpa [S₁,hb] using hcount)
    (by simpa [S₁] using h136) (by simpa [S₁] using h134)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 132) (dst := 145) (saved := 147) (tmp := 134) (by decide)
    result outputTail v₂ S₂ (by simpa [S₂,S₁] using hresult) (by simpa [S₂,S₁,hout] using hcount)
    (by simpa [S₂,S₁] using h147) (by simpa [S₂,S₁] using h134)
  let S₃ : Stacks 148 A := {S₂ with R := Function.update (Function.update S₂.R 132 outputTail) 145 (result++S₂.R 145)}
  obtain ⟨v₄,hu₄,he₄⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 144) (dst := 110) (saved := 147) (tmp := 134) (by decide)
    next parkedTail v₃ S₃ (by simpa [S₃,S₂,S₁] using hparked)
    (by simpa [S₃,S₂,S₁,hnext] using hcount)
    (by simpa [S₃,S₂,S₁] using h147) (by simpa [S₃,S₂,S₁] using h134)
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hr,hb,hout,hnext]; ring) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h144 : k = 144 <;> by_cases h145 : k = 145 <;>
    simp [S₃,S₂,S₁,h110,h132,h144,h145]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
