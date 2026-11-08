module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireResidentColumn

/-! Retire both owned residual streams with one doubled byte clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def retireCyclicResiduals : Pr P 151 Q A U :=
  .seq residentColumnWidth (.seq (umul 2 94 131 135) (.seq (uclear 94)
    (.seq (unaryProduct 121 131 94 134 135)
      (.seq (discardPrefix 94 132 138 134) (clearWords [94,131])))))

def retireCyclicResidualsCost (q s : ℕ) : ℕ :=
  let w := 2*q+8
  (8*q+9)+((4*w+4)+((2*w+2)+(s*(8*w+9)+4+
    ((6*(s*w+s*w)+6)+(2*(2*s*w+2*w)+5)))))

theorem retireCyclicResiduals_exec (q s : ℕ) (right left tail : List (Fin (A+4)))
    (hR : right.length = s*(2*q+8)) (hL : left.length = s*(2*q+8))
    (v : HS 151 Q A U) (S : Stacks 151 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 132 = right++(left++tail))
    (hfresh : ∀ k ∈ [(94 : Fin 151),131,134,135,138], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireCyclicResidualsCost q s ∧
      Exec body retireCyclicResiduals (mk v S) m
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  let w := 2*q+8
  obtain ⟨v₁,hv₁,he₁⟩ := residentColumnWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 135 (by simp))
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,hv₂,he₂⟩ := umul_exec body 2 (a := 94) (b := 131) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 135 (by simp))
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (2*w) tick)}
  have he₂' : Exec body (umul 2 94 131 135) (mk v₁ S₁) (4*w+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hfresh 131 (by simp)] using he₂
  obtain ⟨v₃,hv₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 94 []}
  have hlen₂ : (S₂.R 94).length = w := by simp [S₂,S₁]
  obtain ⟨v₄,m₄,hv₄,hm₄,he₄⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 131) (dst := 94) (t₁ := 134) (t₂ := 135) (by decide) v₃ S₃
    (by simpa [S₃,S₂,S₁] using hfresh 134 (by simp)) (by simpa [S₃,S₂,S₁] using hfresh 135 (by simp))
  let S₄ : Stacks 151 A := {S₃ with R := Function.update S₃.R 94 (List.replicate (2*s*w) tick)}
  have he₄' : Exec body (unaryProduct 121 131 94 134 135) (mk v₃ S₃) m₄ (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,hs,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using he₄
  have hm₄' : m₄ ≤ s*(8*w+9)+4 := by
    have ht : m₄ ≤ s*(4*(2*w)+9)+4 := by simpa [S₃,S₂,S₁,hs] using hm₄
    nlinarith only [ht]
  obtain ⟨v₅,hv₅,he₅⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 132) (trash := 138) (tmp := 134) (by decide)
    (right++left) tail v₄ S₄ (by simpa [S₄,S₃,S₂,S₁,List.append_assoc] using hsrc)
    (by simp [S₄,hR,hL,w]; ring)
    (by simpa [S₄,S₃,S₂,S₁] using hfresh 138 (by simp)) (by simpa [S₄,S₃,S₂,S₁] using hfresh 134 (by simp))
  let S₅ : Stacks 151 A := {S₄ with R := Function.update S₄.R 132 tail}
  obtain ⟨v₆,hv₆,he₆⟩ := clearWords_exec (body := body) [(94 : Fin 151),131] (by decide) v₅ S₅
  have hsum : ([(94 : Fin 151),131].map (fun k => (S₅.R k).length)).sum = 2*s*w+2*w := by
    simp [S₅,S₄,S₃,S₂]
  refine ⟨v₆,(8*q+9)+((4*w+4)+((2*w+2)+(m₄+((6*(right++left).length+6)+(2*(2*s*w+2*w)+5))))),
    hv₆.trans (hv₅.trans (hv₄.trans (hv₃.trans (hv₂.trans hv₁)))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast
      (by rw [hlen₂,hsum]; rfl) ?_⟩
  · simp only [List.length_append,hR,hL]
    exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right hm₄' _) _) _) _
  · apply congrArg (mk v₆)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      by_cases h131 : k = 131
      · subst k; simp [hfresh 131 (by simp)]
      simp [S₅,S₄,S₃,S₂,S₁,h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
