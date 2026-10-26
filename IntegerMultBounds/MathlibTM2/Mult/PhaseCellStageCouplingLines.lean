module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Borrow original RHS and published solution lines for a coupling pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def stageCouplingLines : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 97 94 131 134 135)
    (.seq (copyPrefix 131 110 93 134 135)
      (.seq (copyPrefix 131 132 110 134 135) (uclear 131)))

theorem stageCouplingLines_exec (s w : ℕ) (rhs source rhsTail sourceTail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (hrhs : S.R 110 = rhs++rhsTail) (hsource : S.R 132 = source++sourceTail)
    (hrhsLen : rhs.length = s*w) (hsourceLen : source.length = s*w)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 26*s*w+9*s+26 ∧
      Exec body stageCouplingLines (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 (rhs++S.R 93))
          110 (source++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 97 94 131 134 135) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body)
    (count := 131) (src := 110) (dst := 93) (saved := 134) (tmp := 135) (by decide)
    v₁ S₁ rhs rhsTail (by simpa [S₁] using hrhs) (by simp [S₁,hrhsLen])
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 93 (rhs++S₁.R 93)}
  obtain ⟨v₃,hu₃,he₃⟩ := copyPrefix_exec (body := body)
    (count := 131) (src := 132) (dst := 110) (saved := 134) (tmp := 135) (by decide)
    v₂ S₂ source sourceTail (by simpa [S₂,S₁] using hsource) (by simp [S₂,S₁,hsourceLen])
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 110 (source++S₂.R 110)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 131 v₃ S₃
  refine ⟨v₄,m₁+((10*rhs.length+10)+((10*source.length+10)+(2*(s*w)+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by simp [S₃,S₂,S₁]) ?_⟩
  · rw [hrhsLen,hsourceLen]
    nlinarith only [hm₁']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = 131 <;> simp [S₃,S₂,S₁,h,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
