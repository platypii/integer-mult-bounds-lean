module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Capture the ambient prefix without consuming its physical source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def captureCouplingSource : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 97 94 109 104 105)
    (.seq (copyPrefix 109 110 92 104 105) (uclear 109))

theorem captureCouplingSource_exec (s w : ℕ) (xs tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = xs++tail) (hlen : xs.length = s*w)
    (h92 : S.R 92 = []) (h109 : S.R 109 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ s*(16*w+9)+16 ∧
      Exec body captureCouplingSource (mk v S) m
        (mk v' {S with R := Function.update S.R 92 xs}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 109) (t₁ := 104) (t₂ := 105) (by decide) v S h104 h105
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 109 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 97 94 109 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h109] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body)
    (count := 109) (src := 110) (dst := 92) (saved := 104) (tmp := 105)
    (by decide) v₁ S₁ xs tail (by simpa [S₁] using hsrc)
    (by simp [S₁,hlen]) (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 92 xs}
  have he₂' : Exec body (copyPrefix 109 110 92 104 105) (mk v₁ S₁)
      (10*xs.length+10) (mk v₂ S₂) := by simpa [S₂,S₁,h92] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 109 v₂ S₂
  refine ⟨v₃,m₁+((10*xs.length+10)+(2*(s*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by simp [S₂,S₁]) ?_⟩
  · rw [hlen]
    nlinarith only [hm₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h : r = 109 <;> simp [S₂,S₁,h,h109,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
