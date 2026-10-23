module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceStep

/-! Accumulate reversed affine frames in a separate tape. Reversing the final
accumulator will produce frames in increasing index order with correct bit order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineSourceReverseStepProgram (rg : Fin 12 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (affineSourceStepProgram rg) (moveR (rg 5) dst id)

def affineSourceReverseStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (dst : Fin T)
    (Li Lk i k o : ℕ) :=
  Function.update (Function.update R dst
    ((affineProfileFrames (Li + Lk) [(true, i * k + o)]).reverse ++ R dst)) (rg 0) (binSyms Li (i + 1))

theorem affineSourceReverseStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (dst : Fin T) (hsep : ∀ r, dst ≠ rg r)
    (Li Lk i k o : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ affineSourceFrameCost Li Lk + (4 * Li + 5) + (2 * (Li + Lk + 3) + 2) ∧
      Exec body (affineSourceReverseStepProgram rg dst) (mk v S) steps
        (mk v' { S with R := affineSourceReverseStepBank S.R rg dst Li Lk i k o }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := affineSourceStep_exec body rg hrg Li Lk i k o hi hk hfit v S
    hindex hstride hoffset (fun r h0 h1 h2 _ => hblank r h0 h1 h2)
  let word := affineProfileFrames (A := A) (Li + Lk) [(true, i * k + o)]
  let S₁ : Stacks T A := { S with R := affineSourceStepBank S.R rg Li Lk i k o }
  have hsrc : S₁.R (rg 5) = word := by
    simp [S₁, affineSourceStepBank, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide), word]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) (rg 5) dst (hsep 5).symm id v₁ S₁
  have hlen : word.length = Li + Lk + 3 := by simp [word, affineProfileFrames]; omega
  have hf : movedR S₁.R (rg 5) dst id (S₁.R (rg 5)) = affineSourceReverseStepBank S.R rg dst Li Lk i k o := by
    funext j
    by_cases hj : j = rg 5
    · subst j
      simp [movedR, S₁, affineSourceStepBank, affineSourceReverseStepBank, Function.update_apply,
        hrg.eq_iff, (hsep 5).symm, hblank 5 (by decide) (by decide) (by decide)]
    · by_cases hd : j = dst
      · subst j
        simp [movedR, S₁, affineSourceStepBank, affineSourceReverseStepBank,
          hrg.eq_iff, hsep, hblank 5 (by decide) (by decide) (by decide)]
      · simp [movedR, S₁, affineSourceStepBank, affineSourceReverseStepBank, Function.update_apply, hj, hd]
  rw [hf, hsrc, hlen] at hx₂
  exact ⟨v₂, m₁ + (2 * (Li + Lk + 3) + 2), hu₂.trans hu₁, Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
