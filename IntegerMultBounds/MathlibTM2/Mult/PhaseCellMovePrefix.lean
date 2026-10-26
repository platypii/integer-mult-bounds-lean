module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Relocate an owned prefix in natural order, preserving both borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def movePrefix (count src dst saved tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (transfer count src saved tmp) (moveR saved dst id)

theorem movePrefix_exec {count src dst saved tmp : Fin T}
    (hreg : [count,src,dst,saved,tmp].Nodup) (xs tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = xs++tail)
    (hlen : (S.R count).length = xs.length) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (movePrefix count src dst saved tmp) (mk v S) (6*xs.length+6)
      (mk v' {S with R := Function.update (Function.update S.R src tail) dst (xs++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (count := count) (src := src) (dst := saved) (tmp := tmp) (by regs_nodup) v S xs tail hsrc hlen htmp
  let S₁ : Stacks T A := {S with R := Function.update (Function.update S.R src tail) saved xs.reverse}
  have he₁' : Exec body (transfer count src saved tmp) (mk v S) (4*xs.length+4) (mk v₁ S₁) := by
    simpa [S₁,hsaved] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved dst ‹dst ≠ saved›.symm id v₁ S₁
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast (by simp [S₁]; ring) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hsrc' : k = src <;> by_cases hdst : k = dst <;> by_cases hsaved' : k = saved <;>
    simp_all [S₁,movedR,ne_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
