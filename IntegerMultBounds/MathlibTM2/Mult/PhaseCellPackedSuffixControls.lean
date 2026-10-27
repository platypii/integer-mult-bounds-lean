module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Derive the later-column interval from a borrowed selected-column rank and total count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def packedSuffixControls : Pr P 154 Q A U :=
  .seq (ucopy 107 151 135) (.seq (.act (.push (.rt 151) (fun _ => tick) .done))
    (.seq (ucopy 116 152 135) (usub 151 152 135)))

def packedSuffixControlsCost (n N : ℕ) : ℕ := (4*n+4)+(1+((4*N+4)+(4*(n+1)+4)))

theorem packedSuffixControls_exec (n N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 107).length = n) (hN : (S.R 116).length = N)
    (h135 : S.R 135 = []) (h151 : S.R 151 = []) (h152 : S.R 152 = []) :
    ∃ v', v'.user = v.user ∧ Exec body packedSuffixControls (mk v S) (packedSuffixControlsCost n N)
      (mk v' {S with R := (Function.update (Function.update S.R 151 (List.replicate (n+1) tick))
        152 (List.replicate (N-(n+1)) tick))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 107) (b := 151) (t := 135)
    (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 151 (List.replicate n tick)}
  have he₁' : Exec body (ucopy 107 151 135) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hn,h151] using he₁
  let S₂ : Stacks 154 A := {S with R := Function.update S.R 151 (List.replicate (n+1) tick)}
  have he₂ : Exec body (.act (.push (.rt 151) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,Action.run,update_rt,List.replicate_succ] using
      Exec.act (body := body) (.push (.rt 151) (fun _ => tick) .done) (mk v₁ S₁)
  obtain ⟨v₂,hu₂,he₃⟩ := ucopy_exec body (a := 116) (b := 152) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂] using h135)
  let S₃ : Stacks 154 A := {S₂ with R := Function.update S₂.R 152 (List.replicate N tick)}
  have he₃' : Exec body (ucopy 116 152 135) (mk v₁ S₂) (4*N+4) (mk v₂ S₃) := by
    simpa [S₃,S₂,hN,h152] using he₃
  obtain ⟨v₃,hu₃,he₄⟩ := usub_exec body (a := 151) (b := 152) (t := 135)
    (by decide) (by decide) (by decide) v₂ S₃ (by simpa [S₃,S₂] using h135)
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,packedSuffixControlsCost]
  · apply congrArg (mk v₃)
    simp [S₃,S₂,List.drop_replicate]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
