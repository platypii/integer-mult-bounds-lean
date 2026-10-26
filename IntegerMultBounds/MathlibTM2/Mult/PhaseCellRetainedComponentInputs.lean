module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParkComponent
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentInputs

/-! Prepare the real input and park the imaginary input outside the real solver bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def retainedComponentInputs : Pr P₀ 148 Q A U :=
  .seq (embProg componentReg id splitComponentLine) parkComponent

def retainedComponentInputsCost (s w : ℕ) : ℕ := 20*s*w+9*s+20

theorem retainedComponentInputs_exec (hA : 4 ≤ A) (s w : ℕ) (zs : List GaussianInt)
    (hzlen : zs.length = s) (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w zs++tail)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h136 : S.R 136 = [])
    (h137 : S.R 137 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedComponentInputsCost s w ∧
      Exec (embTab componentReg body) retainedComponentInputs (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R
          110 (cstream A w (zs.map realPartWord)++tail))
          144 (cstream A w (zs.map imagPartWord)++S.R 144))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := splitComponentLine_exec (body := body) hA s w zs hzlen tail
    (embDn componentReg v) (embStk componentReg S)
    (by simpa [embStk,componentReg] using hs) (by simpa [embStk,componentReg] using hw)
    (by simpa [embStk,componentReg] using hsrc) (by simpa [embStk,componentReg] using h131)
    (by simpa [embStk,componentReg] using h134) (by simpa [embStk,componentReg] using h135)
    (by simpa [embStk,componentReg] using h136)
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he₁ v rfl S rfl
  let X := cstream A w (zs.map realPartWord)++tail
  let Y := cstream A w (zs.map imagPartWord)
  let S₁ : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 X) 137 Y}
  have he₂' : Exec (embTab componentReg body) (embProg componentReg id splitComponentLine)
      (mk v S) n₁ (mk v₂ S₁) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    let B := embStk componentReg S
    let B₁ : Stacks 144 A := {B with R := Function.update B.R 110 X}
    rw [embOvr_updR componentReg_injective B₁ S 137 (Y++B.R 137),
      embOvr_updR componentReg_injective B S 110 X,embOvr_stk]
    simp [S₁,X,Y,B,embStk,componentReg,h137]
  obtain ⟨v₃,hu₃,he₃⟩ := parkComponent_exec (body := embTab componentReg body) v₂ S₁
    (by simpa [S₁] using h147)
  refine ⟨v₃,n₁+(4*Y.length+4),hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₂' he₃).cast ?_ ?_⟩
  · have hY : Y.length = s*w := by simp [Y,hzlen]
    rw [hY]
    dsimp [retainedComponentInputsCost,splitComponentLineCost] at *
    nlinarith only [hn₁]
  · simp [S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h137' : k = 137 <;> by_cases h144 : k = 144 <;>
      simp [S₁,h110,h137',h144,h137,X,Y]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
