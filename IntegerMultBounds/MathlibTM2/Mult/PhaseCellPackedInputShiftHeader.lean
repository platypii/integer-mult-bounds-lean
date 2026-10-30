module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftFits

/-! Derive the packed solver's scale shift from retained unary precisions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def packedInputShiftHeader (precision inputPrecision shift tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy precision shift tmp) (.seq (usub inputPrecision shift tmp) (.act (dropTop shift .done)))

theorem packedInputShiftHeader_exec {precision inputPrecision shift tmp : Fin T}
    (hreg : [precision,inputPrecision,shift,tmp].Nodup) (q p : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R precision).length = q) (hp : (S.R inputPrecision).length = p)
    (hshift : S.R shift = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packedInputShiftHeader precision inputPrecision shift tmp) (mk v S) (4*q+4*p+9)
        (mk v' {S with R := Function.update S.R shift (List.replicate (q-p-1) tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹precision ≠ shift› ‹precision ≠ tmp›
    ‹shift ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R shift (List.replicate q tick)}
  have he₁' : Exec body (ucopy precision shift tmp) (mk v S) (4*q+4) (mk v₁ S₁) := by
    simpa [S₁,hq,hshift] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) ‹inputPrecision ≠ shift› ‹inputPrecision ≠ tmp›
    ‹shift ≠ tmp› v₁ S₁ (by simpa [S₁,‹shift ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S with R := Function.update S.R shift (List.replicate (q-p) tick)}
  have he₂' : Exec body (usub inputPrecision shift tmp) (mk v₁ S₁) (4*p+4) (mk v₂ S₂) := by
    simpa [S₁,S₂,‹inputPrecision ≠ shift›,hp] using he₂
  have he₃ : Exec body (.act (dropTop shift .done)) (mk v₂ S₂) 1
      (mk v₂ {S with R := Function.update S.R shift (List.replicate (q-p-1) tick)}) := by
    simpa [S₂,dropTop,Action.run,update_rt,List.tail_replicate] using
      Exec.act (body := body) (dropTop shift .done) (mk v₂ S₂)
  exact ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by omega) rfl⟩

/-- The packed solver's native width is 2q+8. The generated shift represents
half of the original p-grid value exactly and satisfies its signed word fits. -/
theorem packedInputShift_value_fits (p q : ℕ) (hp : p+1 ≤ q)
    (z : GaussianInt) (hz : ‖value p z‖ ≤ 1) :
    value q ((2 : GaussianInt)^(q-p-1)*z) = (1/2 : ℂ)*value p z ∧
      TopFitsZ (2*q+8) ((2 : GaussianInt)^(q-p-1)*z) := by
  have hd : p+1+(q-p-1) = q := by omega
  refine ⟨?_,(inputShift_fits p (q-p-1) (2*q+8) (by omega) z hz).2⟩
  simpa only [hd] using halfGrid_value p (q-p-1) z

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
