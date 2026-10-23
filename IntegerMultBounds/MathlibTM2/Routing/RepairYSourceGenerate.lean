module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryAffineSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairYSourceProfile

/-! Generate the actual first Y repair source profile from binary dimensions,
with no supplied profile or unary count. Only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {T Q A : ℕ} {P U : Type}

theorem repairYSourceGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (src count saved accum dst savedIndex : Fin T)
    (hreg : [src, count, saved, accum, dst, savedIndex].Nodup)
    (hsrcsep : ∀ r, src ≠ rg r) (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (Lc Li Lk : ℕ) (hn : p.n < 2 ^ Lc) (hk : p.K < 2 ^ Lk)
    (hi : p.n ≤ 2 ^ Li) (hwy : p.wy < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lc p.n) (hindex : S.R (rg 0) = binSyms Li 0)
    (hstride : S.R (rg 1) = binSyms Lk p.K) (hoffset : S.R (rg 2) = binSyms (Li + Lk) p.ρ)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ binaryAffineSourceGenerateCost Lc Li Lk p.n ∧
      Exec body (binaryAffineSourceGenerateProgram rg src count saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst ((LiveDescriptorMode.ofKey (some (.Y, 0))).profileFrames p X hG hK active s (Li + Lk) ++ S.R dst) }) := by
  have hfit (j : ℕ) (hj : j < p.n) : (0 + j) * p.K + p.ρ < 2 ^ (Li + Lk) := by
    simpa only [Nat.zero_add, Nat.add_zero, posS, Nat.add_comm] using (repairKeyCoordinates_bound p hK j hj).trans hwy
  obtain ⟨v', steps, hu, ht, hx⟩ := binaryAffineSourceGenerate_exec body rg hrg src count saved accum dst savedIndex
    hreg hsrcsep hcsep hssep hasep hdsep hisep Lc Li Lk p.n 0 p.K p.ρ hn hk (by simpa using hi)
    hfit v S hsrc hindex hstride hoffset hcount hsaved haccum hsavedIndex hblank
  refine ⟨v', steps, hu, ht, ?_⟩
  rw [affineSourceWord_profile] at hx
  rw [repairYSourceProfile_frames p X hG hK active s (Li + Lk)]
  simpa only [Nat.zero_add] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
