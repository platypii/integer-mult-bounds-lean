module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Remove the owned source-line copy after a restoring row pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def retireCouplingLine : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 97 94 131 134 135) (.seq (discardPrefix 131 110 134 135) (uclear 131))

theorem retireCouplingLine_exec (s w : ℕ) (source tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (hsource : S.R 110 = source++tail) (hlen : source.length = s*w)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 12*s*w+9*s+12 ∧
      Exec body retireCouplingLine (mk v S) m (mk v' {S with R := Function.update S.R 110 tail}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 97 94 131 134 135) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 134) (tmp := 135) (by decide) source tail v₁ S₁
    (by simpa [S₁] using hsource) (by simp [S₁,hlen])
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 131 v₂ S₂
  refine ⟨v₃,m₁+((6*source.length+6)+(2*(s*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by simp [S₂,S₁]) ?_⟩
  · rw [hlen]
    nlinarith only [hm₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = 131 <;> simp [S₂,S₁,h,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
