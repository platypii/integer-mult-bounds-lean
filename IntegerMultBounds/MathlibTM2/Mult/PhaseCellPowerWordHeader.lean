module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetPowerWord

/-! Construct a power-of-two word from runtime width and exponent headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def powerWordHeader (width exponent dst parked saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR width dst saved (fun _ => pairSym A false false))
    (setPowerWord exponent dst parked saved tmp)

theorem powerWordHeader_exec {width exponent dst parked saved tmp : Fin T}
    (hreg : [width,exponent,dst,parked,saved,tmp].Nodup) (w e : ℕ) (he : e < w)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : (S.R width).length = w)
    (hexponent : (S.R exponent).length = e) (hdst : S.R dst = [])
    (hparked : S.R parked = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (powerWordHeader width exponent dst parked saved tmp)
      (mk v S) (4*w+4+(8*e+9))
      (mk v' {S with R := Function.update S.R dst (csyms A w (⟨(2 : ℤ)^e,0⟩ : GaussianInt))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body width dst saved (by assumption) (by assumption) (by assumption)
    (fun _ => pairSym A false false) v S hsaved
  let S₁ : Stacks T A := {S with R := Function.update S.R dst (csyms A w 0)}
  have he₁' : Exec body (copyR width dst saved (fun _ => pairSym A false false))
      (mk v S) (4*w+4) (mk v₁ S₁) := by simpa [S₁,csyms_zero,hwidth,hdst] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := setPowerWord_exec (body := body)
    (count := exponent) (src := dst) (parked := parked) (saved := saved) (tmp := tmp)
    (by regs_nodup) w e he [] v₁ S₁ (by simpa [S₁,show exponent ≠ dst by tauto] using hexponent) (by simp [S₁])
    (by simpa [S₁,show parked ≠ dst by tauto] using hparked) (by simpa [S₁,show saved ≠ dst by tauto] using hsaved) (by simpa [S₁,show tmp ≠ dst by tauto] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = dst <;> simp [S₁,hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
