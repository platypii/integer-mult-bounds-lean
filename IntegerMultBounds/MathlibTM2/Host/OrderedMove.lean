module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-! Move a complete right stack through one blank buffer, preserving its order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def moveRightOrdered (src tmp dst : Fin T) : Pr P T Q A U :=
  .seq (moveR src tmp id) (moveR tmp dst id)

theorem moveRightOrdered_exec (src tmp dst : Fin T)
    (hst : src ≠ tmp) (hsd : src ≠ dst) (htd : tmp ≠ dst)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveRightOrdered src tmp dst) (mk v S) (4*(S.R src).length+4)
        (mk v' {S with R := Function.update (Function.update S.R src []) dst (S.R src++S.R dst)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body src tmp hst id v S
  let B : Stacks T A := {S with R := movedR S.R src tmp id (S.R src)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp dst htd id v₁ B
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [B,movedR,htmp]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [B,movedR,Function.update_apply,List.map_id]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Host
