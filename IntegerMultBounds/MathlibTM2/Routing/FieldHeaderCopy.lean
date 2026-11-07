module

public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup

/-! Reuse an obsolete dimension tape for a retained ordinary width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def resetCopy (src dst saved : Fin T) : Pr P T Q A U :=
  .seq (uclear dst) (ucopy src dst saved)

theorem resetCopy_exec (src dst saved : Fin T) (hreg : [src,dst,saved].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) :
    ∃ vf, vf.user = v.user ∧ Exec body (resetCopy src dst saved) (mk v S)
      (2*(S.R dst).length+4*(S.R src).length+6)
      (mk vf {S with R := Function.update S.R dst (List.replicate (S.R src).length tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) dst v S
  let F : Stacks T A := {S with R := Function.update S.R dst []}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) ‹src ≠ dst› ‹src ≠ saved› ‹dst ≠ saved› v₁ F
    (by simp [F,‹dst ≠ saved›.symm,hsaved])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp only [F,Function.update_of_ne ‹src ≠ dst›]; omega
  · simp [F,‹src ≠ dst›]

theorem resetCopy_pushBound (src dst saved : Fin T) :
    mnNativePushBound 2 (resetCopy (P := P) (Q := Q) (A := A) (U := U) src dst saved) := by
  simp [resetCopy,uclear,ucopy,umulSym,scanR,keepIn,pushN,drainR,popDo,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy
