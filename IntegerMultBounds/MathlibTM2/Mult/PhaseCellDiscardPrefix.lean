module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Consume an owned counted prefix and restore both scratch registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def discardPrefix (count src trash tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src trash tmp) (uclear trash)

theorem discardPrefix_exec {count src trash tmp : Fin T}
    (hreg : [count,src,trash,tmp].Nodup) (xs tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = xs++tail)
    (hlen : (S.R count).length = xs.length) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (discardPrefix count src trash tmp) (mk v S) (6*xs.length+6)
        (mk v' { S with R := Function.update S.R src tail }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body) hreg v S xs tail hsrc hlen htmp
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src tail) trash xs.reverse) }
  have he₁' : Exec body (transfer count src trash tmp) (mk v S) (4*xs.length+4) (mk v₁ S₁) := by
    simpa [S₁, htrash] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body trash v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast (by simp [S₁]; ring) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hkt : k = trash
    · subst k; simp [‹src ≠ trash›.symm, htrash]
    simp [S₁, Function.update_apply, hkt]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
