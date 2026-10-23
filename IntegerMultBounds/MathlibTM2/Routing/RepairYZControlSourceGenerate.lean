module

public import IntegerMultBounds.MathlibTM2.Routing.RepairYZSourceProfile

/-! Execute YZ control profile generation from raw activity bits and binary control
operands, restoring every borrowed tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {T Q A : ℕ} {P U : Type}

theorem repairYZControlSourceGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved accum dst savedIndex : Fin T)
    (hreg : [src, saved, accum, dst, savedIndex].Nodup)
    (hcsep : ∀ r, src ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (hcz : ∀ r, src ≠ zr r) (hsz : ∀ r, saved ≠ zr r)
    (haz : ∀ r, accum ≠ zr r) (hiz : ∀ r, savedIndex ≠ zr r)
    (hzIndex : ∀ r, zr r ≠ rg 0)
    (Lw Li Lk : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hk : p.G < 2 ^ Lk)
    (hi : p.n ≤ 2 ^ Li) (hcontrol : p.wy + 2 * p.wc ≤ 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn active).map bitSymbol) (hindex : S.R (rg 0) = binSyms Li 0)
    (hstride : S.R (rg 1) = binSyms Lk p.G) (hoffset : S.R (rg 2) = binSyms (Li + Lk) (p.wy + p.wc))
    (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * optionalAffineSourceIterationCost Lw Li Lk + 2 * p.n +
        2 * (p.n * (Li + Lk + 3)) + 16 * Li + 22 ∧
      Exec body (optionalAffineSourceGenerateProgram rg zr src saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst ((LiveDescriptorMode.ofKey (some (.YZ, 1))).profileFrames p X hG hK active s (Li + Lk) ++ S.R dst) }) := by
  have hfit (j : ℕ) (hj : j < (List.ofFn active).length) :
      (0 + j) * p.G + (p.wy + p.wc) < 2 ^ (Li + Lk) := by
    have hjn : j < p.n := by simpa using hj
    have hm := Nat.mul_lt_mul_of_pos_right hjn hG
    change j * p.G < p.wc at hm
    simp only [Nat.zero_add]
    omega
  obtain ⟨v', steps, hu, ht, hx⟩ := optionalAffineSourceGenerate_exec body rg hrg zr hzr hdst
    src saved accum dst savedIndex hreg hcsep hssep hasep hdsep hisep hcz hsz haz hiz hzIndex
    Lw Li Lk 0 p.G (p.wy + p.wc) (List.ofFn active) hwidth hk (by simpa using hi) hfit
    v S hsrc hindex hstride hoffset hsaved haccum hsavedIndex hblank hwidthInput hunary hzeroScratch
  refine ⟨v', steps, hu, by simpa using ht, ?_⟩
  rw [repairYZControlSourceProfile_frames p X hG hK active s Li Lk]
  exact hx

end
end IntegerMultBounds.MathlibTM2.Routing
