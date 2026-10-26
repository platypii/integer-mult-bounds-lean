module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Reconstruct the fixed-point word width from retained outer precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingHeaderWidth : Pr P₀ 144 Q A U :=
  .seq (ucopy 119 94 135) (.seq (ucopy 119 94 135) (.act (pushN 94 (fun _ => tick) 8 .done)))

theorem couplingHeaderWidth_exec (q : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hq : (S.R 119).length = q) (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body couplingHeaderWidth (mk v S) (8*q+9)
      (mk v' {S with R := Function.update S.R 94 (List.replicate (2*q+8) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 119) (b := 94) (t := 135)
    (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 94 (List.replicate q tick)}
  have he₁' : Exec body (ucopy 119 94 135) (mk v S) (4*q+4) (mk v₁ S₁) := by
    simpa [S₁,hq,h94] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 119) (b := 94) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S with R := Function.update S.R 94 (List.replicate (q+q) tick)}
  have he₂' : Exec body (ucopy 119 94 135) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hq,← List.replicate_append_replicate] using he₂
  have he₃ := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 .done) (mk v₂ S₂)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by omega) ?_⟩
  rw [pushN_run]
  simp only [S₂,Action.run,Function.update_self,Function.update_idem]
  rw [List.replicate_append_replicate]
  have hn : 8+(q+q) = 2*q+8 := by omega
  rw [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
