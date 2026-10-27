module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Reconstruct the fixed-point word width from retained outer precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def generateWordWidth (precision width tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (ucopy precision width tmp) (.seq (ucopy precision width tmp) (.act (pushN width (fun _ => tick) 8 .done)))

theorem generateWordWidth_exec {precision width tmp : Fin T}
    (hreg : [precision,width,tmp].Nodup) (q : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R precision).length = q) (hwidth : S.R width = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (generateWordWidth precision width tmp) (mk v S) (8*q+9)
      (mk v' {S with R := Function.update S.R width (List.replicate (2*q+8) tick)}) := by
  have hpw : precision ≠ width := by intro h; subst width; simp at hreg
  have hpt : precision ≠ tmp := by intro h; subst tmp; simp at hreg
  have hwt : width ≠ tmp := by intro h; subst tmp; simp at hreg
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := precision) (b := width) (t := tmp)
    hpw hpt hwt v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R width (List.replicate q tick)}
  have he₁' : Exec body (ucopy precision width tmp) (mk v S) (4*q+4) (mk v₁ S₁) := by
    simpa [S₁,hq,hwidth] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := precision) (b := width) (t := tmp)
    hpw hpt hwt v₁ S₁ (by simpa [S₁,hwt.symm] using htmp)
  let S₂ : Stacks T A := {S with R := Function.update S.R width (List.replicate (q+q) tick)}
  have he₂' : Exec body (ucopy precision width tmp) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hpw,hq,← List.replicate_append_replicate] using he₂
  have he₃ := Exec.act (body := body) (pushN width (fun _ => tick) 8 .done) (mk v₂ S₂)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by omega) ?_⟩
  rw [pushN_run]
  simp only [S₂,Action.run,Function.update_self,Function.update_idem]
  rw [List.replicate_append_replicate]
  have hn : 8+(q+q) = 2*q+8 := by omega
  rw [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
