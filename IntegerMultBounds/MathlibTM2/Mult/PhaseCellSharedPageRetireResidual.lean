module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire recovery's owned residual prefix using retained row and word-width masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageRetireResidual : Pr P 240 Q A U :=
  .seq (unaryProduct 121 160 231 232 233)
    (.seq (discardPrefix 231 110 232 233) (uclear 231))

def sharedPageRetireResidualCost (s w : ℕ) : ℕ := s*(12*w+9)+12

theorem sharedPageRetireResidual_exec (s w : ℕ) (residual tail : List (Fin (A+4)))
    (hlen : residual.length = s*w) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hs : (S.R 121).length = s) (hw : (S.R 160).length = w)
    (hsource : S.R 110 = residual++tail)
    (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageRetireResidualCost s w ∧
      Exec body sharedPageRetireResidual (mk v S) n
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 160) (dst := 231) (t₁ := 232) (t₂ := 233) (by decide) v S h232 h233
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 231 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 160 231 232 233) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hs,hw,h231,List.append_nil] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa only [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 231) (src := 110) (trash := 232) (tmp := 233) (by decide)
    residual tail v₁ S₁ (by simpa [S₁] using hsource) (by simp [S₁,hlen])
    (by simpa [S₁] using h232) (by simpa [S₁] using h233)
  let S₂ : Stacks 240 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 231 v₂ S₂
  have hclock : (S₂.R 231).length = s*w := by simp [S₂,S₁]
  refine ⟨v₃,n₁+((6*residual.length+6)+(2*(S₂.R 231).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen,hclock]
    dsimp only [sharedPageRetireResidualCost]
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi110 : i = 110 <;> by_cases hi231 : i = 231 <;> simp [S₂,S₁,hi110,hi231,h231]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
