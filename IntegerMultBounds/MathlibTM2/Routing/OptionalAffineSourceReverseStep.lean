module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceStep

/-! Accumulate optional affine frames in reverse, preserving activity archives
and advancing the index even when the source is inactive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceReverseStepProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceStepProgram rg zr src saved) (moveR (rg 5) dst id)

def optionalAffineSourceReverseStepBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (src saved dst : Fin T) (Li Lk i k o : ℕ)
    (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R src rest)
    saved (bitSymbol enabled :: R saved)) dst
    ((affineProfileFrames (Li + Lk) [(enabled, if enabled then i * k + o else 0)]).reverse ++ R dst))
    (rg 0) (binSyms Li (i + 1))

theorem optionalAffineSourceReverseStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (dst : Fin T) (hdsep : ∀ r, dst ≠ rg r) (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + 1 + (4 * Li + 5) + (2 * (Li + Lk + 3) + 2) ∧
      Exec body (optionalAffineSourceReverseStepProgram rg zr src saved dst) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceReverseStepBank S.R rg src saved dst Li Lk i k o enabled rest }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceStep_exec body rg hrg zr hzr hdst
    src saved hss hsrcRg hsavedRg hsrcZr hsavedZr Lw Li Lk i k o hwidth hi hk hfit
    enabled rest v S hsrc hindex hstride hoffset (fun r h0 h1 h2 _ => hblank r h0 h1 h2)
    hwidthInput hunary hzeroScratch
  let word := affineProfileFrames (A := A) (Li + Lk) [(enabled, if enabled then i * k + o else 0)]
  let S₁ : Stacks T A := { S with R := optionalAffineSourceStepBank S.R rg src saved Li Lk i k o enabled rest }
  have hsrcFrame : S₁.R (rg 5) = word := by
    simp [S₁, optionalAffineSourceStepBank, optionalAffineSourceCallBank, hrg.eq_iff,
      hblank 5 (by decide) (by decide) (by decide), word]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) (rg 5) dst (hdsep 5).symm id v₁ S₁
  have hlen : word.length = Li + Lk + 3 := by simp [word, affineProfileFrames]; omega
  have hf : movedR S₁.R (rg 5) dst id (S₁.R (rg 5)) =
      optionalAffineSourceReverseStepBank S.R rg src saved dst Li Lk i k o enabled rest := by
    funext j
    by_cases hj : j = rg 5
    · subst j
      simp [movedR, S₁, optionalAffineSourceStepBank, optionalAffineSourceCallBank,
        optionalAffineSourceReverseStepBank, Function.update_apply, hrg.eq_iff,
        (hdsep 5).symm, (hsrcRg 5).symm, (hsavedRg 5).symm,
        hblank 5 (by decide) (by decide) (by decide)]
    · by_cases hd : j = dst
      · subst j
        simp [movedR, S₁, optionalAffineSourceStepBank, optionalAffineSourceCallBank,
          optionalAffineSourceReverseStepBank, hrg.eq_iff, hdsep, hdsrc, hdsaved,
          hblank 5 (by decide) (by decide) (by decide)]
      · simp [movedR, S₁, optionalAffineSourceStepBank, optionalAffineSourceCallBank,
          optionalAffineSourceReverseStepBank, Function.update_apply, hj, hd]
  rw [hf, hsrcFrame, hlen] at hx₂
  exact ⟨v₂, m₁ + (2 * (Li + Lk + 3) + 2), hu₂.trans hu₁,
    Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
