module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs

/-! Generate cyclic slice byte controls from the retained original-coordinate endpoints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def cyclicSliceControls : Pr P 224 Q A U :=
  .seq (ucopy 145 141 143) (.seq (usub 144 141 143)
    (.seq (unaryProduct 144 94 0 3 4) (.seq (unaryProduct 141 94 1 3 4)
      (.seq (unaryProduct 146 94 2 3 4) (uclear 141)))))

def cyclicSliceControlsCost (a left right w : ℕ) : ℕ :=
  (4*(a+left)+4)+(4*a+4)+((a+left+right)*(4*w+9)+12)+(2*left+2)

theorem cyclicSliceControls_exec (a left right w : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (ha : (S.R 144).length = a) (hleft : (S.R 145).length = a+left)
    (hright : (S.R 146).length = right) (hw : (S.R 94).length = w)
    (hfresh : ∀ k ∈ ([(0 : Fin 224),1,2,3,4,141,143]), S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicSliceControlsCost a left right w ∧
      Exec body cyclicSliceControls (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          0 (List.replicate (a*w) tick)) 1 (List.replicate (left*w) tick)) 2 (List.replicate (right*w) tick))}) := by
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec body (a := 145) (b := 141) (t := 143)
    (by decide) (by decide) (by decide) v S (hfresh 143 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 141 (List.replicate (a+left) tick)}
  have he₁' : Exec body (ucopy 145 141 143) (mk v S) (4*(a+left)+4) (mk v₁ S₁) := by
    simpa [S₁,hleft,hfresh 141 (by simp)] using he₁
  obtain ⟨v₂,hv₂,he₂⟩ := usub_exec body (a := 144) (b := 141) (t := 143)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 143 (by simp))
  let S₂ : Stacks 224 A := {S with R := Function.update S.R 141 (List.replicate left tick)}
  have he₂' : Exec body (usub 144 141 143) (mk v₁ S₁) (4*a+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,ha] using he₂
  obtain ⟨v₃,m₃,hv₃,hm₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := 144) (b := 94) (dst := 0) (t₁ := 3) (t₂ := 4) (by decide) v₂ S₂
    (by simpa [S₂] using hfresh 3 (by simp)) (by simpa [S₂] using hfresh 4 (by simp))
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 0 (List.replicate (a*w) tick)}
  have he₃' : Exec body (unaryProduct 144 94 0 3 4) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,ha,hw,hfresh 0 (by simp)] using he₃
  have hm₃' : m₃ ≤ a*(4*w+9)+4 := by simpa [S₂,ha,hw] using hm₃
  obtain ⟨v₄,m₄,hv₄,hm₄,he₄⟩ := unaryProduct_exec (body := body)
    (a := 141) (b := 94) (dst := 1) (t₁ := 3) (t₂ := 4) (by decide) v₃ S₃
    (by simpa [S₃,S₂] using hfresh 3 (by simp)) (by simpa [S₃,S₂] using hfresh 4 (by simp))
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 1 (List.replicate (left*w) tick)}
  have he₄' : Exec body (unaryProduct 141 94 1 3 4) (mk v₃ S₃) m₄ (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,hw,hfresh 1 (by simp)] using he₄
  have hm₄' : m₄ ≤ left*(4*w+9)+4 := by simpa [S₃,S₂,hw] using hm₄
  obtain ⟨v₅,m₅,hv₅,hm₅,he₅⟩ := unaryProduct_exec (body := body)
    (a := 146) (b := 94) (dst := 2) (t₁ := 3) (t₂ := 4) (by decide) v₄ S₄
    (by simpa [S₄,S₃,S₂] using hfresh 3 (by simp)) (by simpa [S₄,S₃,S₂] using hfresh 4 (by simp))
  let S₅ : Stacks 224 A := {S₄ with R := Function.update S₄.R 2 (List.replicate (right*w) tick)}
  have he₅' : Exec body (unaryProduct 146 94 2 3 4) (mk v₄ S₄) m₅ (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,hw,hright,hfresh 2 (by simp)] using he₅
  have hm₅' : m₅ ≤ right*(4*w+9)+4 := by simpa [S₄,S₃,S₂,hw,hright] using hm₅
  obtain ⟨v₆,hv₆,he₆⟩ := uclear_exec body 141 v₅ S₅
  refine ⟨v₆,(4*(a+left)+4)+((4*a+4)+(m₃+(m₄+(m₅+(2*left+2))))),
    hv₆.trans (hv₅.trans (hv₄.trans (hv₃.trans (hv₂.trans hv₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆))))).cast ?_ ?_⟩
  · unfold cyclicSliceControlsCost
    nlinarith only [hm₃',hm₄',hm₅']
  · simp [S₅,S₄,S₃,S₂]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h141 : k = 141
    · subst k; simp [hfresh 141 (by simp)]
    · simp [S₅,S₄,S₃,S₂,h141,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
