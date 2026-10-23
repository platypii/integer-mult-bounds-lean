module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedSourceWords

/-! Emit a complete repeated source group, then advance the group index once.
The group width does not cause repeated selector arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGroupStepProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (rp : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceGroupProgram rg zr rp) (countIter (rg 0) (rg 8) (rg 11))

def optionalAffineSourceGroupStepBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T) (Li Lk i k o g : ℕ) (enabled : Bool) :=
  Function.update (Function.update R (rp 3)
    (affineProfileFrames (Li + Lk) (List.replicate g (enabled, if enabled then i * k + o else 0)) ++ R (rp 3)))
    (rg 0) (binSyms Li (i + 1))

theorem optionalAffineSourceGroupStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (hdsep : ∀ r, rp 3 ≠ rg r)
    (Lg g : ℕ) (hg : g < 2 ^ Lg)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (v : HS T Q A U) (S : Stacks T A) (hflag : v.flag = enabled)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (hgroup : S.R (rp 0) = binSyms Lg g)
    (hcount : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + binaryWordRepeatCost Lg g (Li + Lk + 3) + (2 * (Li + Lk + 3) + 2) + (4 * Li + 5) ∧
      Exec body (optionalAffineSourceGroupStepProgram rg zr rp) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceGroupStepBank S.R rg rp Li Lk i k o g enabled }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceGroup_exec body rg hrg zr hzr hdst rp hrp hsep
    Lg g hg Lw Li Lk i k o hwidth hi hk hfit enabled v S hflag hindex hstride hoffset
    hblank hwidthInput hunary hzeroScratch hgroup hcount hsaved hwork htmp hctmp
  rw [wordCopies_affineProfileFrame] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rp 3) (affineProfileFrames (Li + Lk) (List.replicate g (enabled, if enabled then i * k + o else 0)) ++ S.R (rp 3)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := countIter_exec (body := body) (W := Li) (j := i)
    (hrg.ne (by decide : (0 : Fin 12) ≠ 8)) (rg 11) v₁ G
    (by simp [G, (hdsep 0).symm, hindex])
    (by simp [G, (hdsep 8).symm, hblank 8 (by decide) (by decide) (by decide)])
  exact ⟨v₂, m₁ + (4 * Li + 5), hu₂.trans hu₁, Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
