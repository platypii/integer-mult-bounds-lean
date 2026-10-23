module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCall

/-! Advance the source index after either activity branch, so inactive entries
retain their position in the source enumeration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceStepProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceCallProgram rg zr src saved)
    (countIter (rg 0) (rg 8) (rg 11))

def optionalAffineSourceStepBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (src saved : Fin T) (Li Lk i k o : ℕ)
    (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (optionalAffineSourceCallBank R src saved (rg 5)
    (Li + Lk) i k o enabled rest) (rg 0) (binSyms Li (i + 1))

theorem optionalAffineSourceStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + 1 + (4 * Li + 5) ∧
      Exec body (optionalAffineSourceStepProgram rg zr src saved) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceStepBank S.R rg src saved Li Lk i k o enabled rest }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceCall_exec body rg hrg zr hzr hdst
    src saved hss hsrcRg hsavedRg hsrcZr hsavedZr Lw Li Lk i k o hwidth hi hk hfit
    enabled rest v S hsrc hindex hstride hoffset hblank hwidthInput hunary hzeroScratch
  let S₁ : Stacks T A := { S with R := optionalAffineSourceCallBank S.R src saved (rg 5) (Li + Lk) i k o enabled rest }
  have hkeep (r : Fin 12) (h5 : r ≠ 5) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, optionalAffineSourceCallBank, hrg.eq_iff, h5,
      (hsrcRg r).symm, (hsavedRg r).symm]
  obtain ⟨v₂, hu₂, hx₂⟩ := countIter_exec (body := body) (W := Li) (j := i)
    (hrg.ne (by decide : (0 : Fin 12) ≠ 8)) (rg 11) v₁ S₁
    ((hkeep 0 (by decide)).trans hindex)
    ((hkeep 8 (by decide)).trans (hblank 8 (by decide) (by decide) (by decide) (by decide)))
  exact ⟨v₂, m₁ + (4 * Li + 5), hu₂.trans hu₁,
    Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
