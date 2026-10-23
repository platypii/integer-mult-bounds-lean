module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairAControlSourceProfile

/-! Generate the actual first A source profile from raw activity and a binary
group size. Compute each control selector once per group and restore all inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

theorem repairAControlSourceGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved accum dst savedIndex : Fin T)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (hpRg : ∀ r, rp 3 ≠ rg r)
    (hsrcRp : ∀ r, src ≠ rp r) (hsavedRp : ∀ r, saved ≠ rp r)
    (haRp : ∀ r, accum ≠ rp r) (hpIndex : ∀ r, rp r ≠ rg 0)
    (hiRp : ∀ r, savedIndex ≠ rp r)
    (hreg : [src, saved, accum, dst, savedIndex].Nodup)
    (hcsep : ∀ r, src ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (hcz : ∀ r, src ≠ zr r) (hsz : ∀ r, saved ≠ zr r)
    (haz : ∀ r, accum ≠ zr r) (hiz : ∀ r, savedIndex ≠ zr r)
    (hzIndex : ∀ r, zr r ≠ rg 0)
    (Lg : ℕ) (hg : p.G < 2 ^ Lg)
    (Lw Li Lk : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hk : p.G < 2 ^ Lk)
    (hi : p.n ≤ 2 ^ Li) (hcontrol : 2 * p.wc ≤ 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn active).map bitSymbol) (hindex : S.R (rg 0) = binSyms Li 0)
    (hstride : S.R (rg 1) = binSyms Lk p.G) (hoffset : S.R (rg 2) = binSyms (Li + Lk) p.wc)
    (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (houtput : S.R (rp 3) = []) (hgroup : S.R (rp 0) = binSyms Lg p.G)
    (hcount : S.R (rp 1) = []) (hrepeatSaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * optionalAffineSourceGroupIterationCost Lg p.G Lw Li Lk + 2 * p.n +
        2 * (p.n * (p.G * (Li + Lk + 3))) + 16 * Li + 22 ∧
      Exec body (optionalAffineSourceGroupGenerateProgram rg zr rp src saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst ((LiveDescriptorMode.ofKey (some (.A, 0))).profileFrames p X hG hK active s (Li + Lk) ++ S.R dst) }) := by
  have hfit (j : ℕ) (hj : j < (List.ofFn active).length) :
      (0 + j) * p.G + p.wc < 2 ^ (Li + Lk) := by
    have hjn : j < p.n := by simpa using hj
    have hm := Nat.mul_lt_mul_of_pos_right hjn hG
    change j * p.G < p.wc at hm
    simp only [Nat.zero_add]
    omega
  obtain ⟨v', steps, hu, ht, hx⟩ := optionalAffineSourceGroupGenerate_exec body rg hrg zr hzr hdst
    src saved accum dst savedIndex rp hrp hsep hpRg hsrcRp hsavedRp haRp hpIndex hiRp
    hreg hcsep hssep hasep hdsep hisep hcz hsz haz hiz hzIndex Lg p.G hg
    Lw Li Lk 0 p.G p.wc (List.ofFn active) hwidth hk (by simpa using hi) hfit
    v S hsrc hindex hstride hoffset hsaved haccum hsavedIndex hblank hwidthInput hunary hzeroScratch
    houtput hgroup hcount hrepeatSaved hwork htmp hctmp
  refine ⟨v', steps, hu, by simpa using ht, ?_⟩
  rw [optionalAffineSourceGroupWord_profile] at hx
  rw [repairAControlSourceProfile_frames p X hG hK active s (Li + Lk)]
  simpa only [Nat.zero_add] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
