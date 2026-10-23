module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupCall
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates

/-! Accumulate each completed source group in reverse on a separate tape.
One final reversal will restore both group order and each frame's bit order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGroupReverseProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (rp : Fin 7 → Fin T) (src saved accum : Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceGroupCallProgram rg zr rp src saved) (moveR (rp 3) accum id)

def optionalAffineSourceGroupReverseBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (_rp : Fin 7 → Fin T) (src saved accum : Fin T)
    (Li Lk i k o g : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R src rest)
    saved (bitSymbol enabled :: R saved)) accum
    ((affineProfileFrames (Li + Lk) (List.replicate g (enabled, if enabled then i * k + o else 0))).reverse ++ R accum))
    (rg 0) (binSyms Li (i + 1))

theorem optionalAffineSourceGroupReverse_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (hdsep : ∀ r, rp 3 ≠ rg r)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (hsrcRp : ∀ r, src ≠ rp r) (hsavedRp : ∀ r, saved ≠ rp r)
    (accum : Fin T) (haRg : ∀ r, accum ≠ rg r) (haRp : ∀ r, accum ≠ rp r)
    (hasrc : accum ≠ src) (hasaved : accum ≠ saved)
    (Lg g : ℕ) (hg : g < 2 ^ Lg)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (houtput : S.R (rp 3) = [])
    (hgroup : S.R (rp 0) = binSyms Lg g)
    (hcount : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + binaryWordRepeatCost Lg g (Li + Lk + 3) + (2 * (Li + Lk + 3) + 2) + (4 * Li + 5) + 1 + (2 * (g * (Li + Lk + 3)) + 2) ∧
      Exec body (optionalAffineSourceGroupReverseProgram rg zr rp src saved accum) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceGroupReverseBank S.R rg rp src saved accum Li Lk i k o g enabled rest }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceGroupCall_exec body rg hrg zr hzr hdst rp hrp hsep hdsep
    src saved hss hsrcRg hsavedRg hsrcZr hsavedZr hsrcRp hsavedRp
    Lg g hg Lw Li Lk i k o hwidth hi hk hfit enabled rest v S hsrc hindex hstride hoffset
    hblank hwidthInput hunary hzeroScratch hgroup hcount hsaved hwork htmp hctmp
  let word := affineProfileFrames (A := A) (Li + Lk) (List.replicate g (enabled, if enabled then i * k + o else 0))
  let G : Stacks T A := { S with R := optionalAffineSourceGroupCallBank S.R rg rp src saved Li Lk i k o g enabled rest }
  have hf : G.R (rp 3) = word := by
    simp [G, optionalAffineSourceGroupCallBank, optionalAffineSourceGroupStepBank,
      hdsep 0, (hsrcRp 3).symm, (hsavedRp 3).symm, houtput, word]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) (rp 3) accum (haRp 3).symm id v₁ G
  have hbank : movedR G.R (rp 3) accum id (G.R (rp 3)) =
      optionalAffineSourceGroupReverseBank S.R rg rp src saved accum Li Lk i k o g enabled rest := by
    funext j
    by_cases hj : j = rp 3
    · subst j
      simp [movedR, optionalAffineSourceGroupReverseBank, hdsep 0, (haRp 3).symm,
        (hsrcRp 3).symm, (hsavedRp 3).symm, houtput]
    · by_cases ha : j = accum
      · subst j
        simp [movedR, G, optionalAffineSourceGroupCallBank, optionalAffineSourceGroupStepBank,
          optionalAffineSourceGroupReverseBank, haRg, haRp, hasrc, hasaved, hdsep 0,
          (hsrcRp 3).symm, (hsavedRp 3).symm, houtput]
      · simp [movedR, G, optionalAffineSourceGroupCallBank, optionalAffineSourceGroupStepBank,
          optionalAffineSourceGroupReverseBank, Function.update_apply, hj, ha]
  have hlen : word.length = g * (Li + Lk + 3) := by
    rw [affineProfileFrames_length, List.length_replicate]
  rw [hbank, hf, hlen] at hx₂
  exact ⟨v₂, m₁ + (2 * (g * (Li + Lk + 3)) + 2), hu₂.trans hu₁,
    Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
