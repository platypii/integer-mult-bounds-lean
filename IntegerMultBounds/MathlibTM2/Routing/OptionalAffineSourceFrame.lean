module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryInactiveProfileFrame

/-! Select an active affine source frame or an inactive frame from a live flag.
Both branches restore their operands and scratch; only the shared output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceFrameProgram (rg : Fin 12 → Fin T) (zr : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .cond (·.flag) (affineSourceFrameProgram rg) (binaryInactiveProfileFrameProgram zr)

def optionalAffineSourceFrameCost (Lw Li Lk : ℕ) :=
  max (affineSourceFrameCost Li Lk) (Lw * (4 * (Li + Lk) + 11) + 8 * (Li + Lk) + 15) + 1

theorem optionalAffineSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (v : HS T Q A U) (S : Stacks T A) (hflag : v.flag = enabled)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk ∧
      Exec body (optionalAffineSourceFrameProgram rg zr) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 5) (affineProfileFrames (Li + Lk) [(enabled, if enabled then i * k + o else 0)] ++ S.R (rg 5)) }) := by
  cases enabled with
  | false =>
    obtain ⟨v', steps, hu, ht, hx⟩ := binaryInactiveProfileFrame_exec body zr hzr Lw (Li + Lk) hwidth v S
      hwidthInput hunary hzeroScratch
    rw [hdst] at hx
    refine ⟨v', steps + 1, hu, ?_, Exec.cond_false (by simpa only [mk_var] using hflag) hx⟩
    have hm := le_max_right (affineSourceFrameCost Li Lk) (Lw * (4 * (Li + Lk) + 11) + 8 * (Li + Lk) + 15)
    unfold optionalAffineSourceFrameCost
    omega
  | true =>
    obtain ⟨v', steps, hu, ht, hx⟩ := affineSourceFrame_exec body rg hrg Li Lk i k o hi hk hfit v S
      hindex hstride hoffset hblank
    refine ⟨v', steps + 1, hu, ?_, Exec.cond_true (by simpa only [mk_var] using hflag) hx⟩
    have hm := le_max_left (affineSourceFrameCost Li Lk) (Lw * (4 * (Li + Lk) + 11) + 8 * (Li + Lk) + 15)
    unfold optionalAffineSourceFrameCost
    omega

end IntegerMultBounds.MathlibTM2.Routing
