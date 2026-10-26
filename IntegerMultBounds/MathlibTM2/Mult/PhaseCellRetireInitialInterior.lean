module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginalPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire the initial interior line after its residual has been computed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def retireInitialInterior : Pr P₀ 148 Q A U :=
  .seq originalInputClock (.seq (discardPrefix 131 132 147 134) (clearWords [94,131]))

def retireInitialInteriorCost (q s : ℕ) : ℕ := 12*s*(2*q+8)+9*s+12*q+40

theorem retireInitialInterior_exec (q s : ℕ) (xs tail : List (Fin (A+4)))
    (hlen : xs.length = s*(2*q+8)) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 132 = xs++tail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = [])
    (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireInitialInteriorCost q s ∧
      Exec (embTab componentReg body) retireInitialInterior (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 tail)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := originalInputClock_exec (body := body)
    q s v S hq hs h94 h131 h134 h135
  let S₂ : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 94 (List.replicate (2*q+8) tick))
    131 (List.replicate (s*(2*q+8)) tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := embTab componentReg body)
    (count := 131) (src := 132) (trash := 147) (tmp := 134) (by decide) xs tail v₁ S₂
    (by simpa [S₂] using hsource)
    (by simp [S₂,hlen]) (by simpa [S₂] using h147) (by simpa [S₂] using h134)
  let S₃ : Stacks 148 A := {S₂ with R := (Function.update S₂.R 132 tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := embTab componentReg body)
    [(94 : Fin 148),131] (by decide) v₂ S₃
  have hsum : ([(94 : Fin 148),131].map (fun r => (S₃.R r).length)).sum =
      (2*q+8)+s*(2*q+8) := by simp [S₃,S₂]
  refine ⟨v₃,n₁+((6*xs.length+6)+(2*((2*q+8)+s*(2*q+8))+5)),
    hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [retireInitialInteriorCost]
    rw [hlen]
    nlinarith only [hn₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      simp [S₃,S₂,h94',h131',h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
