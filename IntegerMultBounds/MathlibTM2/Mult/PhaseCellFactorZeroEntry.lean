module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroWords

/-! Emit a factor-row padding zero at the actual retained precision and release its width control. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def factorZeroEntry : Pr P 154 Q A U :=
  .seq (generateWordWidth 119 131 135) (.seq
    (copyR 131 140 134 (fun _ => pairSym A false false)) (uclear 131))

def factorZeroEntryCost (q : ℕ) : ℕ := (8*q+9)+((4*(2*q+8)+4)+(2*(2*q+8)+2))

theorem factorZeroEntry_exec (q : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body factorZeroEntry (mk v S) (factorZeroEntryCost q)
      (mk v' {S with R := Function.update S.R 140 (csyms A (2*q+8) 0++S.R 140)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 131) (tmp := 135) (by decide) q v S hq h131 h135
  let w := 2*q+8
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 131 (List.replicate w tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec body 131 140 134 (by decide) (by decide) (by decide)
    (fun _ => pairSym A false false) v₁ S₁ (by simpa [S₁] using h134)
  let output := csyms A w 0++S.R 140
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₂' : Exec body (copyR 131 140 134 (fun _ => pairSym A false false))
      (mk v₁ S₁) (4*w+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,output,csyms_zero] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 131 v₂ S₂
  have hlen : (S₂.R 131).length = w := by simp [S₂,S₁]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk131 : k = 131 <;> by_cases hk140 : k = 140 <;>
    simp [S₂,S₁,output,w,hk131,hk140,h131]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
