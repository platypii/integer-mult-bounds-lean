module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceEncoding

/-! Execute the actual key source-profile generator from raw tagged source choices.
Every raw input and scratch tape is restored; only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

theorem repairKeySourceGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (rg : Fin 4 → Fin 13 → Fin T) (hrg : ∀ tag, Function.Injective (rg tag))
    (src saved index localOffset tmp dst accum out : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, dst, accum, out].Nodup)
    (hsrc : ∀ tag j, src ≠ rg tag j) (hsaved : ∀ tag j, saved ≠ rg tag j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ tag j, dst ≠ rg tag j) (hacc : ∀ tag j, accum ≠ rg tag j)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (hz5 : ∀ tag j, zr j ≠ rg tag 5)
    (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (hzIndex : ∀ j, zr j ≠ index) (hzLocal : ∀ j, zr j ≠ localOffset)
    (hzAcc : ∀ j, accum ≠ zr j)
    (Lw Li Lk : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hk : p.K < 2 ^ Lk) (hn : p.n ≤ 2 ^ Li)
    (hw : p.wy + 2 * p.wc + X < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = gatedSelectedSourceWords Li Lk (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (houtput : S.R dst = [])
    (hstride : ∀ tag, S.R (rg tag 1) = binSyms Lk p.K)
    (hbase : ∀ tag, S.R (rg tag 2) = binSyms (Li + Lk) (SlotSource.regionBase p tag))
    (hblank : ∀ tag j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg tag j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = [])
    (harchive : S.R saved = []) (haccum : S.R accum = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * gatedSelectedSourceIterationCost Lw Li Lk +
        2 * (p.n * (Li + (Li + Lk) + 5)) + 2 * (p.n * (Li + Lk + 3)) + 6 ∧
      Exec body (gatedSelectedSourceGenerateProgram rg zr src saved index localOffset tmp dst accum out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out ((LiveDescriptorMode.ofKey none).profileFrames p X hG hK active s (Li + Lk) ++ S.R out) }) := by
  have hfit : ∀ x ∈ List.ofFn (fun c => (s c).gatedChoice (active c)),
      x.index < 2 ^ Li ∧ x.position p.K (SlotSource.regionBase p) < 2 ^ (Li + Lk) := by
    intro x hx
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hx
    refine ⟨(s c).gatedChoice_index_fit (active c) Li hn, ?_⟩
    rw [SlotSource.gatedChoice_position]
    exact (sourceWire p X (s c)).isLt.trans hw
  obtain ⟨v', steps, hu, ht, hx⟩ := gatedSelectedSourceGenerate_exec body rg hrg
    src saved index localOffset tmp dst accum out hreg hsrc hsaved hindexReg hlocalReg hsep hacc
    zr hzr hdst hz5 hsrcZr hsavedZr hzIndex hzLocal hzAcc Lw Li Lk p.K hwidth (SlotSource.regionBase p) (List.ofFn (fun c => (s c).gatedChoice (active c))) hk hfit
    v S hraw hindex hlocal htmp houtput hstride hbase hblank hwidthInput hunary hzeroScratch harchive haccum
  refine ⟨v', steps, hu, by simpa using ht, ?_⟩
  rw [repairKeySourceProfile_encoded p X hG hK active s Li Lk] at hx
  exact hx

end
end IntegerMultBounds.MathlibTM2.Routing
