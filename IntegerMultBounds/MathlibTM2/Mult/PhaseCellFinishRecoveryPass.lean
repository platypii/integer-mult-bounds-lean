module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveRecoveryOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Park computed interior words and restore both shared input streams. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def finishRecoveryPass : Pr P 148 Q A U :=
  .seq archiveRecoveryOutput (embProg componentReg id retireAmbientSource)

theorem finishRecoveryPass_exec (q s : ℕ) (words field residual input : List (Fin (A+4)))
    (hwords : words.length = s*(2*q+8)) (hresidual : residual.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (houtput : S.R 132 = words++field) (hinput : S.R 110 = residual++input)
    (hfresh : ∀ k ∈ [(94 : Fin 148),131,134,135,143], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ archiveResidualPrefixCost q s+retireAmbientSourceCost q s ∧
      Exec (embTab componentReg body) finishRecoveryPass (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          132 field) 147 (words++S.R 147)) 110 input)}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := archiveRecoveryOutput_exec (body := body)
    q s words field hwords v S hq hs houtput hfresh
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update S.R 132 field) 147 (words++S.R 147))}
  let E := embStk componentReg S₁
  obtain ⟨vi,m₂,hvi,hm₂,hei⟩ := retireAmbientSource_exec (body := body)
    q s residual input (embDn componentReg v₁) E
    (by simpa [E,embStk,componentReg,S₁] using hq)
    (by simpa [E,embStk,componentReg,S₁] using hs)
    (by simpa [E,embStk,componentReg,S₁] using hinput) hresidual
    (by simpa [E,embStk,componentReg,S₁] using hfresh 94 (by simp))
    (by simpa [E,embStk,componentReg,S₁] using hfresh 131 (by simp))
    (by simpa [E,embStk,componentReg,S₁] using hfresh 134 (by simp))
    (by simpa [E,embStk,componentReg,S₁] using hfresh 135 (by simp))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := componentReg) (ι := id)
    (body' := embTab componentReg body) componentReg_injective (fun p => rfl) hei v₁ rfl S₁ rfl
  have he₂' : Exec (embTab componentReg body) (embProg componentReg id retireAmbientSource)
      (mk v₁ S₁) m₂ (mk v₂ {S₁ with R := Function.update S₁.R 110 input}) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR componentReg_injective,embOvr_stk]
    rfl
  exact ⟨v₂,m₁+m₂,hu₂.trans (hvi.trans hv₁),Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
