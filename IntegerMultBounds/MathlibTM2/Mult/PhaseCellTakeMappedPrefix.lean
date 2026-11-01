module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! Consume a prefix and map its symbols while restoring their order.
Projection and routing therefore share one transfer instead of separate scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def takeMappedPrefix (count src dst saved tmp : Fin T) (f : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  .seq (transfer count src saved tmp) (moveR saved dst f)

theorem takeMappedPrefix_exec {count src dst saved tmp : Fin T}
    (hreg : [count,src,dst,saved,tmp].Nodup) (f : Fin (A+4) → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A+4)))
    (hsrc : S.R src = xs++tail) (hlen : (S.R count).length = xs.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (takeMappedPrefix count src dst saved tmp f) (mk v S) (6*xs.length+6)
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs.map f++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v S xs tail hsrc hlen htmp
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R src tail)
    saved (xs.reverse++S.R saved))}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved dst (Ne.symm ‹dst ≠ saved›) f v₁ J
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [J,hsaved]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [J,movedR,Function.update_apply,hsaved,List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
