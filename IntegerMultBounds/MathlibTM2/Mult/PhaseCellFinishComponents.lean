module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishComponentsCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate and release the counters for final complex pairing and source release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def finishComponents : Pr P₀ 148 Q A U :=
  .seq (embProg componentReg id couplingHeaderWidth) (.seq (unaryProduct 121 94 131 134 135)
    (.seq finishComponentsCore (clearWords [94,131])))

def finishComponentsCost (q s : ℕ) : ℕ := 34*s*(2*q+8)+9*s+12*q+60

theorem finishComponents_exec (hA : 4 ≤ A) (q s : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s)
    (recovery rhs tail savedTail outputTail : List (Fin (A+4)))
    (hr : recovery.length = s*(2*q+8)) (hb : rhs.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A) (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = recovery++(rhs++tail))
    (hx : S.R 145 = cstream A (2*q+8) xs++savedTail) (hy : S.R 132 = cstream A (2*q+8) ys++outputTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h140 : S.R 140 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ finishComponentsCost q s ∧
      Exec (embTab componentReg body) finishComponents (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail) 145 savedTail)
          132 (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  let w := 2*q+8
  obtain ⟨v₁,hu₁,he₁⟩ := couplingHeaderWidth_exec (body := body) q (embDn componentReg v) (embStk componentReg S)
    (by simpa [embStk,componentReg] using hq) (by simpa [embStk,componentReg] using h94)
    (by simpa [embStk,componentReg] using h135)
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he₁ v rfl S rfl
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  have he₂' : Exec (embTab componentReg body) (embProg componentReg id couplingHeaderWidth)
      (mk v S) (8*q+9) (mk v₂ S₁) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR componentReg_injective (embStk componentReg S) S 94 (List.replicate w tick),embOvr_stk]
    rfl
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := embTab componentReg body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v₂ S₁
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (s*w) tick)}
  have he₃' : Exec (embTab componentReg body) (unaryProduct 121 94 131 134 135)
      (mk v₂ S₁) n₃ (mk v₃ S₂) := by simpa [S₂,S₁,hs,h131] using he₃
  have hn₃' : n₃ ≤ s*(4*w+9)+4 := by simpa [S₁,hs] using hn₃
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := finishComponentsCore_exec (body := embTab componentReg body) hA s w xs ys hxlen hylen
    recovery rhs tail savedTail outputTail hr hb v₃ S₂ (by simp [S₂])
    (by simpa [S₂,S₁] using hsrc) (by simpa [S₂,S₁] using hx) (by simpa [S₂,S₁] using hy)
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h136)
    (by simpa [S₂,S₁] using h140) (by simpa [S₂,S₁] using h147)
  let Z := cstream A w (List.zipWith pairComponentWord xs ys)++outputTail
  let S₃ : Stacks 148 A := {S₂ with R := (Function.update (Function.update (Function.update S₂.R 110 tail) 145 savedTail) 132 Z)}
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := embTab componentReg body) [(94 : Fin 148),131] (by decide) v₄ S₃
  have hsum : ([(94 : Fin 148),131].map (fun r => (S₃.R r).length)).sum = w+s*w := by simp [S₃,S₂,S₁]
  refine ⟨v₅,(8*q+9)+(n₃+(n₄+(2*(w+s*w)+5))),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [finishComponentsCost,w] at *
    nlinarith only [hn₃',hn₄]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h131' : k = 131 <;>
      simp [S₃,S₂,S₁,Z,w,h94',h131',h94,h131,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
