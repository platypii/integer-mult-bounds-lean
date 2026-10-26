module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire both generated coupling prefixes and their owned row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def retireCouplingOperands : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 102 94 109 104 105)
    (.seq (discardPrefix 109 110 106 105)
      (.seq (discardPrefix 109 111 106 105) (clearWords [109,102])))

theorem retireCouplingOperands_exec (L w : ℕ) (xs as tailX tailA : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hL : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hx : S.R 110 = xs++tailX) (ha : S.R 111 = as++tailA)
    (hxlen : xs.length = L*w) (halen : as.length = L*w)
    (h109 : S.R 109 = []) (h104 : S.R 104 = [])
    (h105 : S.R 105 = []) (h106 : S.R 106 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 18*L*w+11*L+21 ∧
      Exec body retireCouplingOperands (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          110 tailX) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 102) (b := 94) (dst := 109) (t₁ := 104) (t₂ := 105) (by decide) v S h104 h105
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 109 (List.replicate (L*w) tick)}
  have he₁' : Exec body (unaryProduct 102 94 109 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,h109] using he₁
  have hm₁' : m₁ ≤ L*(4*w+9)+4 := by simpa [hL,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 109) (src := 110) (trash := 106) (tmp := 105) (by decide)
    xs tailX v₁ S₁ (by simpa [S₁] using hx) (by simp [S₁,hxlen])
    (by simpa [S₁] using h106) (by simpa [S₁] using h105)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 110 tailX}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 109) (src := 111) (trash := 106) (tmp := 105) (by decide)
    as tailA v₂ S₂ (by simpa [S₂,S₁] using ha) (by simp [S₂,S₁,halen])
    (by simpa [S₂,S₁] using h106) (by simpa [S₂,S₁] using h105)
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 111 tailA}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(109 : Fin 117),102] (by decide) v₃ S₃
  have hsum : ([(109 : Fin 117),102].map (fun k => (S₃.R k).length)).sum = L*w+L := by
    simp [S₃,S₂,S₁,hL]
  refine ⟨v₄,m₁+((6*xs.length+6)+((6*as.length+6)+(2*(L*w+L)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · rw [hxlen,halen]
    nlinarith only [hm₁']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h : r = 109 <;> simp [S₃,S₂,S₁,h,h109,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
