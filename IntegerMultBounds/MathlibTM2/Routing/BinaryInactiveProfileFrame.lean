module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySelectorZeroFrame
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileLoop

/-! Generate one inactive source-profile frame from a binary selector width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryInactiveProfileFrameProgram (rg : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .seq (binarySelectorZeroFrameProgram rg)
    (.seq (.act (.push (.rt (rg .dst)) (fun _ => separator) .done))
      (.act (.push (.rt (rg .dst)) (fun _ => bitSymbol false) .done)))

theorem binaryInactiveProfileFrame_exec (body : P → Pr P T Q A U)
    (rg : BinaryZeroReg → Fin T) (hrg : Function.Injective rg)
    (Lw L : ℕ) (hL : L < 2 ^ Lw) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms Lw L) (hunary : S.R (rg .unary) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ Lw * (4 * L + 11) + 8 * L + 15 ∧
      Exec body (binaryInactiveProfileFrameProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (affineProfileFrames L [(false, 0)] ++ S.R (rg .dst)) }) := by
  obtain ⟨v', m, hu, hm, hx⟩ := binarySelectorZeroFrame_exec body rg hrg Lw L hL v S hwidth hunary hscratch
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) (binSyms L 0 ++ separator :: S.R (rg .dst)) }
  let S₂ : Stacks T A := { S with R := Function.update S.R (rg .dst) (separator :: binSyms L 0 ++ separator :: S.R (rg .dst)) }
  have hp : (Action.push (.rt (rg .dst)) (fun _ => separator) .done : Act T Q A U).run (mk v' S₁) = mk v' S₂ := by
    simp [Action.run, update_rt, S₁, S₂]
  have hq : (Action.push (.rt (rg .dst)) (fun _ => bitSymbol false) .done : Act T Q A U).run (mk v' S₂) =
      mk v' { S with R := Function.update S.R (rg .dst) (affineProfileFrames L [(false, 0)] ++ S.R (rg .dst)) } := by
    simp [Action.run, update_rt, S₂, affineProfileFrames, binSyms]
  exact ⟨v', m + (1 + 1), hu, by omega,
    Exec.seq hx (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v' S₁))
      (hq ▸ Exec.act (body := body) _ (mk v' S₂)))⟩

end IntegerMultBounds.MathlibTM2.Routing
