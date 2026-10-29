module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-! Map an owned complete line with one temporary stack and restore its order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def mapOwnedLine (src tmp : Fin T) (f : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  .seq (moveR src tmp f) (moveR tmp src id)

theorem mapOwnedLine_exec (src tmp : Fin T) (hne : src ≠ tmp) (f : Fin (A+4) → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (mapOwnedLine src tmp f) (mk v S) (4*(S.R src).length+4)
        (mk v' {S with R := Function.update S.R src ((S.R src).map f)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body src tmp hne f v S
  let B : Stacks T A := {S with R := movedR S.R src tmp f (S.R src)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp src hne.symm id v₁ B
  have hlen : (B.R tmp).length = (S.R src).length := by simp [B,movedR,htmp]
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast (by rw [hlen]; omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hsrc : k = src
  · subst k; simp [B,movedR,hne,hne.symm,htmp]
  by_cases htemp : k = tmp
  · subst k; simp [B,movedR,hne,hne.symm,htmp]
  · simp [B,movedR,hsrc,htemp]

end IntegerMultBounds.MathlibTM2.Host
