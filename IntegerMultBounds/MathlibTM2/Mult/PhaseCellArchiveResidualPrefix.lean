module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginalPrefix

/-! Archive a residual prefix while exposing the same original RHS for another solve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def archiveResidualPrefix : Pr P₀ 148 Q A U :=
  .seq originalInputClock (.seq (movePrefix 131 110 132 147 134) (clearWords [94,131]))

def archiveResidualPrefixCost (q s : ℕ) : ℕ := 12*s*(2*q+8)+9*s+12*q+40

theorem archiveResidualPrefix_exec (q s : ℕ) (xs tail : List (Fin (A+4)))
    (hlen : xs.length = s*(2*q+8)) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = xs++tail)
    (hfresh : ∀ k ∈ [(94 : Fin 148),131,134,135,147], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ archiveResidualPrefixCost q s ∧
      Exec (embTab componentReg body) archiveResidualPrefix (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 110 tail) 132 (xs++S.R 132)}) := by
  let w := 2*q+8
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := originalInputClock_exec (body := body) q s v S hq hs
    (hfresh 94 (by simp)) (hfresh 131 (by simp)) (hfresh 134 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 148 A := {S with R := (Function.update
    (Function.update S.R 94 (List.replicate w tick)) 131 (List.replicate (s*w) tick))}
  obtain ⟨v₂,hv₂,he₂⟩ := movePrefix_exec (body := embTab componentReg body)
    (count := 131) (src := 110) (dst := 132) (saved := 147) (tmp := 134) (by decide)
    xs tail v₁ S₁ (by simpa [S₁] using hsrc) (by simp [S₁,hlen,w])
    (by simpa [S₁] using hfresh 147 (by simp)) (by simpa [S₁] using hfresh 134 (by simp))
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 110 tail) 132 (xs++S₁.R 132)}
  obtain ⟨v₃,hv₃,he₃⟩ := clearWords_exec (body := embTab componentReg body) [(94 : Fin 148),131] (by decide) v₂ S₂
  have hsum : ([(94 : Fin 148),131].map (fun k => (S₂.R k).length)).sum = w+s*w := by simp [S₂,S₁]
  refine ⟨v₃,m₁+((6*xs.length+6)+(2*(w+s*w)+5)),hv₃.trans (hv₂.trans hv₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hlen]
    change m₁ ≤ 8*q+9+(s*(4*w+9)+4) at hm₁
    dsimp [archiveResidualPrefixCost,w] at *
    nlinarith only [hm₁]
  · apply congrArg (mk v₃)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      by_cases h131 : k = 131
      · subst k; simp [hfresh 131 (by simp)]
      simp [S₂,S₁,h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
