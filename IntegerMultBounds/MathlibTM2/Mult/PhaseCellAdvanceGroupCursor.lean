module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Advance a binary-origin stream and its owned unary count together. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def advanceGroupCursor (width origins count trash tmp : Fin T) : Pr P T Q A U :=
  .seq (discardPrefix width origins trash tmp) (.act (dropTop count .done))

theorem advanceGroupCursor_exec {width origins count trash tmp : Fin T}
    (hreg : [width,origins,count,trash,tmp].Nodup) (V : ℕ)
    (word tail cs : List (Fin (A+4))) (hword : word.length = V)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (horigins : S.R origins = word++tail)
    (hcount : S.R count = tick::cs) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (advanceGroupCursor width origins count trash tmp) (mk v S) (6*V+7)
        (mk v' {S with R := (Function.update (Function.update S.R origins tail) count cs)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body)
    (count := width) (src := origins) (trash := trash) (tmp := tmp)
    (by regs_nodup) word tail v S horigins (hwidth.trans hword.symm) htrash htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R origins tail}
  have hc : S₁.R count = tick::cs := by simpa [S₁, ‹origins ≠ count›.symm] using hcount
  have he₂ : Exec body (.act (dropTop count .done)) (mk v₁ S₁) 1
      (mk v₁ {S₁ with R := Function.update S₁.R count cs}) := by
    simpa [dropTop,Action.run,update_rt,hc] using
      Exec.act (body := body) (dropTop count .done) (mk v₁ S₁)
  exact ⟨v₁,hu₁,(Exec.seq he₁ he₂).cast (by rw [hword]) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
