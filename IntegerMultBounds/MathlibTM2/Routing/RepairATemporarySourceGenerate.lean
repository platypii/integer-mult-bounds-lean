module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCounterSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairATemporarySourceProfile

/-! Generate the actual second A repair source profile from binary dimensions,
with no supplied profile or unary count. Only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {T Q A : ℕ} {P U : Type}

theorem repairATemporarySourceGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (src count saved accum dst savedIndex : Fin T)
    (hreg : [src, count, saved, accum, dst, savedIndex].Nodup)
    (hsrcsep : ∀ r, src ≠ rg r) (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (Lc L : ℕ) (hn : p.wc < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lc p.wc) (hindex : S.R (rg 0) = binSyms L 0)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 5, r ≠ 0 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ binaryCounterSourceGenerateCost Lc L p.wc ∧
      Exec body (binaryCounterSourceGenerateProgram rg src count saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst ((LiveDescriptorMode.ofKey (some (.A, 1))).profileFrames p X hG hK active s L ++ S.R dst) }) := by
  obtain ⟨v', steps, hu, ht, hx⟩ := binaryCounterSourceGenerate_exec body rg hrg src count saved accum dst savedIndex
    hreg hsrcsep hcsep hssep hasep hdsep hisep Lc L p.wc 0 hn v S hsrc hindex
    hcount hsaved haccum hsavedIndex hblank
  refine ⟨v', steps, hu, ht, ?_⟩
  rw [counterSourceWord_profile] at hx
  rw [repairATemporarySourceProfile_frames p X hG hK active s L]
  simpa only [Nat.zero_add, Par.wc] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
