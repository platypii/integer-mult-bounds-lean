module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceFrame

/-! One active source-profile iteration computes and emits the selector, then
advances its internal index. Every other register is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineSourceStepProgram (rg : Fin 12 → Fin T) : Pr P T Q A U :=
  .seq (affineSourceFrameProgram rg) (countIter (rg 0) (rg 8) (rg 11))

def affineSourceStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (Li Lk i k o : ℕ) :=
  Function.update (Function.update R (rg 5)
    (affineProfileFrames (Li + Lk) [(true, i * k + o)] ++ R (rg 5))) (rg 0) (binSyms Li (i + 1))

theorem affineSourceStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (Li Lk i k o : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ affineSourceFrameCost Li Lk + (4 * Li + 5) ∧
      Exec body (affineSourceStepProgram rg) (mk v S) steps
        (mk v' { S with R := affineSourceStepBank S.R rg Li Lk i k o }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := affineSourceFrame_exec body rg hrg Li Lk i k o hi hk hfit v S hindex hstride hoffset hblank
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg 5) (affineProfileFrames (Li + Lk) [(true, i * k + o)] ++ S.R (rg 5)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := countIter_exec (body := body) (W := Li) (j := i) (hrg.ne (by decide : (0 : Fin 12) ≠ 8)) (rg 11) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hindex])
    (by simp [S₁, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide) (by decide)])
  exact ⟨v₂, m₁ + (4 * Li + 5), hu₂.trans hu₁, Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
