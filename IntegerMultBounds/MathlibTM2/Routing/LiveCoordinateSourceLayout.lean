module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileCoordinateGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveSourceBases

/-! Install the coordinate-stream compiler in the existing live descriptor bank.
Its high boundary is the generated outer-tape-5 operand; all other operands and
scratch reuse existing live roles. No additional physical tapes are introduced. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def liveCoordinateSourceRole : Fin 21 → LiveDescriptorRole 11 :=
  ![.coordinate .loadTmp, .base 0, .base 1, .stride 1, .base 9,
    .profile (.coordinate (.arithmetic .index)), .coordinate .target, .coordinate .entry,
    .profile (.coordinate (.arithmetic .product)), .profile (.coordinate .wire),
    .profile (.coordinate (.arithmetic .muls)), .profile (.coordinate (.arithmetic .mult)),
    .profile .loadTmp, .profile (.coordinate (.arithmetic .tx)),
    .profile (.coordinate (.arithmetic .ty)), .profile (.coordinate (.arithmetic .tz)),
    .coordinate .gap, .profileSaved, .archive, .coordinate .dst, .profile .activity]

def liveCoordinateSourceReg (r : Fin 21) : Fin (liveInactiveProfileT repairT 11) :=
  if r = 2 then liveInactiveProfileAux 5 else
    liveInactiveProfileCore (liveDescriptorAux (liveCoordinateSourceRole r))

theorem liveCoordinateSourceReg_injective : Function.Injective liveCoordinateSourceReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [liveCoordinateSourceReg, liveCoordinateSourceRole,
      liveInactiveProfileAux_core, liveInactiveProfileCore_aux,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff]

theorem liveCoordinateSourceAux_separate (i : Fin 7) (hi : i ≠ 5) (r : Fin 21) :
    liveInactiveProfileAux i ≠ liveCoordinateSourceReg r := by
  fin_cases r <;> simp_all [liveCoordinateSourceReg, liveInactiveProfileAux_injective.eq_iff,
    liveInactiveProfileAux_core]

theorem liveCoordinateSourceRaw_separate (i : Fin repairT) (r : Fin 21) :
    liveZSourceActivity i ≠ liveCoordinateSourceReg r := by
  fin_cases r <;> simp [liveZSourceActivity, liveCoordinateSourceReg, liveCoordinateSourceRole,
    liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff, liveDescriptorCore_aux]

theorem liveCoordinateSourceSetup {A : ℕ}
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (S : Stacks (liveInactiveProfileT repairT 11) A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (liveInactiveProfileCore (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hhigh : S.R (liveInactiveProfileAux 5) = binSyms w.coordinateBits (p.ρ + p.n * p.K)) :
    SourceCoordinateSetup liveCoordinateSourceReg w.indexBits w.strideBits p.ρ (p.ρ + p.n * p.K) p.K S := by
  have hr (r : Fin 21) : S.R (liveInactiveProfileCore (liveDescriptorAux (liveCoordinateSourceRole r))) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveCoordinateSourceRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [liveCoordinateSourceRole])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [liveCoordinateSourceReg, liveCoordinateSourceRole, LiveDescriptorWidths.coordinateBits] using
      (hr 1).trans (selectedSourceBase_rho p X hG hK active s w)
  · simpa [liveCoordinateSourceReg, LiveDescriptorWidths.coordinateBits] using hhigh
  · simpa [liveCoordinateSourceReg, liveCoordinateSourceRole] using
      (hr 3).trans (selectedSourceStride p X hG hK active s w)
  · simpa [liveCoordinateSourceReg, liveCoordinateSourceRole, LiveDescriptorWidths.coordinateBits] using
      (hr 4).trans (selectedSourceBase_zero p X hG hK active s w)
  · simpa [liveCoordinateSourceReg, liveCoordinateSourceRole, liveDescriptorData] using congrArg List.length (hr 5)
  · intro r hrmem
    fin_cases r <;> simp_all [liveCoordinateSourceReg, liveCoordinateSourceRole, liveDescriptorData]

end
end IntegerMultBounds.MathlibTM2.Routing
