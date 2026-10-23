module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileLoop

/-! Emit an active source-profile frame from a binary selector operand.
The selector and copy scratch are restored; only the output grows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryActiveProfileFrameProgram (src dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => separator) .done))
    (.seq (bcopy src dst tmp work)
      (.seq (.act (.push (.rt dst) (fun _ => separator) .done))
        (.act (.push (.rt dst) (fun _ => bitSymbol true) .done))))

theorem binaryActiveProfileFrame_exec (body : P → Pr P T Q A U)
    (src dst tmp work : Fin T) (hreg : [src, dst, tmp, work].Nodup) (L q : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L q)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryActiveProfileFrameProgram src dst tmp work) (mk v S) (6 * L + 9)
        (mk v' { S with R := Function.update S.R dst (affineProfileFrames L [(true, q)] ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (separator :: S.R dst) }
  have hp : (Action.push (.rt dst) (fun _ => separator) .done : Act T Q A U).run (mk v S) = mk v S₁ := by
    simp [Action.run, update_rt, S₁]
  obtain ⟨v₁, hu₁, hx₁⟩ := bcopy_exec body hreg v S₁
    (by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹dst ≠ work›, hwork])
  have hs : S₁.R src = binSyms L q := by simp [S₁, ‹src ≠ dst›, hsrc]
  rw [hs, length_binSyms] at hx₁
  let S₂ : Stacks T A := { S with R := Function.update S.R dst (binSyms L q ++ separator :: S.R dst) }
  have hf : Function.update S₁.R dst (binSyms L q ++ S₁.R dst) = S₂.R := by simp [S₁, S₂]
  rw [hf] at hx₁
  let S₃ : Stacks T A := { S with R := Function.update S.R dst (separator :: binSyms L q ++ separator :: S.R dst) }
  have hsep : (Action.push (.rt dst) (fun _ => separator) .done : Act T Q A U).run (mk v₁ S₂) = mk v₁ S₃ := by
    simp [Action.run, update_rt, S₂, S₃]
  have hbit : (Action.push (.rt dst) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v₁ S₃) =
      mk v₁ { S with R := Function.update S.R dst (affineProfileFrames L [(true, q)] ++ S.R dst) } := by
    simp [Action.run, update_rt, S₃, affineProfileFrames, binSyms]
  refine ⟨v₁, hu₁, ?_⟩
  exact Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S))
    (Exec.seq hx₁ (Exec.seq (hsep ▸ Exec.act (body := body) _ (mk v₁ S₂))
      (hbit ▸ Exec.act (body := body) _ (mk v₁ S₃))))) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
