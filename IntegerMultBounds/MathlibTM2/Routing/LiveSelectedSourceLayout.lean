module

public import IntegerMultBounds.MathlibTM2.Routing.RepairKeySourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveZSourceLayout

/-! Selected-source arithmetic reuses the live descriptor scratch bank. Two
outer tapes hold region bases; they are read-only operands, not new tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
noncomputable section

def selectedScratchRole : Fin 13 → LiveDescriptorRole 11 :=
  ![.coordinate .loadTmp, .stride 1, .base 0,
    .coordinate .target, .profile (.coordinate (.arithmetic .product)),
    .profile (.coordinate .wire), .coordinate .entry,
    .profile (.coordinate (.arithmetic .muls)), .profile (.coordinate (.arithmetic .mult)),
    .profile (.coordinate (.arithmetic .tx)), .profile (.coordinate (.arithmetic .ty)),
    .profile (.coordinate (.arithmetic .tz)), .profile .loadTmp]

def liveSelectedSourceReg (tag : Fin 4) (r : Fin 13) :
    Fin (liveInactiveProfileT repairT 11) :=
  if r = 2 then
    match tag.val with
    | 0 => liveInactiveProfileCore (liveDescriptorAux (.base 9))
    | 1 => liveInactiveProfileCore (liveDescriptorAux (.base 0))
    | 2 => liveInactiveProfileAux 5
    | _ => liveInactiveProfileAux 6
  else liveInactiveProfileCore (liveDescriptorAux (selectedScratchRole r))

theorem liveSelectedSourceReg_injective (tag : Fin 4) :
    Function.Injective (liveSelectedSourceReg tag) := by
  intro i j h
  fin_cases tag <;> fin_cases i <;> fin_cases j <;>
    simp_all [liveSelectedSourceReg, selectedScratchRole,
      liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff, liveInactiveProfileAux_core, liveInactiveProfileCore_aux]

theorem liveSelectedSourceReg_index (tag : Fin 4) :
    liveSelectedSourceReg tag 0 = liveInactiveProfileCore
      (liveDescriptorAux (.coordinate .loadTmp)) := by
  simp [liveSelectedSourceReg, selectedScratchRole]

theorem liveSelectedSourceReg_local (tag : Fin 4) :
    liveSelectedSourceReg tag 3 = liveInactiveProfileCore (liveDescriptorAux (.coordinate .target)) := by
  simp [liveSelectedSourceReg, selectedScratchRole]

def liveSelectedSourceZeroReg (r : BinaryZeroReg) : Fin (liveInactiveProfileT repairT 11) :=
  match r with
  | .dst => liveInactiveProfileAux 1
  | _ => liveZSourceZeroReg r

theorem liveSelectedSourceZeroReg_injective : Function.Injective liveSelectedSourceZeroReg := by
  intro i j h
  cases i <;> cases j <;>
    simp_all [liveSelectedSourceZeroReg, liveZSourceZeroReg, liveZSourceZeroRole,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff,
      liveInactiveProfileAux_core, liveInactiveProfileCore_aux]

theorem liveSelectedSourceAux_separate (i : Fin 7) (hi5 : i ≠ 5) (hi6 : i ≠ 6)
    (tag : Fin 4) (r : Fin 13) : liveInactiveProfileAux i ≠ liveSelectedSourceReg tag r := by
  fin_cases tag <;> fin_cases r <;>
    simp_all [liveSelectedSourceReg, selectedScratchRole, liveInactiveProfileAux_core,
      liveInactiveProfileAux_injective.eq_iff]

theorem liveSelectedSourceZero_position (tag : Fin 4) (r : BinaryZeroReg) :
    liveSelectedSourceZeroReg r ≠ liveSelectedSourceReg tag 5 := by
  cases r <;> simp [liveSelectedSourceZeroReg, liveSelectedSourceReg, selectedScratchRole,
    liveZSourceZeroReg, liveZSourceZeroRole, liveInactiveProfileAux_core,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff]

theorem liveSelectedSourceZero_index (tag : Fin 4) (r : BinaryZeroReg) :
    liveSelectedSourceZeroReg r ≠ liveSelectedSourceReg tag 0 := by
  cases r <;> simp [liveSelectedSourceZeroReg, liveSelectedSourceReg, selectedScratchRole,
    liveZSourceZeroReg, liveZSourceZeroRole, liveInactiveProfileAux_core,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff]

theorem liveSelectedSourceZero_local (tag : Fin 4) (r : BinaryZeroReg) :
    liveSelectedSourceZeroReg r ≠ liveSelectedSourceReg tag 3 := by
  cases r <;> simp [liveSelectedSourceZeroReg, liveSelectedSourceReg, selectedScratchRole,
    liveZSourceZeroReg, liveZSourceZeroRole, liveInactiveProfileAux_core,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff]

theorem liveSelectedSourceRaw_reg (src : Fin repairT) (tag : Fin 4) (r : Fin 13) :
    liveZSourceActivity src ≠ liveSelectedSourceReg tag r := by
  fin_cases tag <;> fin_cases r <;>
    simp [liveZSourceActivity, liveSelectedSourceReg, selectedScratchRole,
      liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorCore_aux]

theorem liveSelectedSourceRaw_zero (src : Fin repairT) (r : BinaryZeroReg) :
    liveZSourceActivity src ≠ liveSelectedSourceZeroReg r := by
  cases r <;> simp [liveSelectedSourceZeroReg, liveZSourceActivity, liveZSourceZeroReg,
    liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff, liveDescriptorCore_aux]

theorem liveSelectedSourceAux_zero (i : Fin 7) (hi : i ≠ 1) (r : BinaryZeroReg) :
    liveInactiveProfileAux i ≠ liveSelectedSourceZeroReg r := by
  cases r <;> simp_all [liveSelectedSourceZeroReg, liveZSourceZeroReg,
    liveInactiveProfileAux_core, liveInactiveProfileAux_injective.eq_iff]

theorem liveSelectedSourceOutput_reg (j : Fin 11) (tag : Fin 4) (r : Fin 13) :
    liveInactiveProfileCore (liveDescriptorAux (.input j)) ≠ liveSelectedSourceReg tag r := by
  fin_cases tag <;> fin_cases r <;>
    simp [liveSelectedSourceReg, selectedScratchRole, liveInactiveProfileCore_aux,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff]

theorem liveSelectedSourceOutput_zero (j : Fin 11) (r : BinaryZeroReg) :
    liveInactiveProfileCore (liveDescriptorAux (.input j)) ≠ liveSelectedSourceZeroReg r := by
  cases r <;> simp [liveSelectedSourceZeroReg, liveZSourceZeroReg, liveZSourceZeroRole,
    liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff,
    liveDescriptorAux_injective.eq_iff]

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem selectedScratchRole_data {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (r : Fin 13) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    liveDescriptorData (A := A) p X hG hK active s repairLiveMode w (selectedScratchRole r) = [] := by
  fin_cases r <;> simp_all [selectedScratchRole, liveDescriptorData]

theorem selectedSourceBase_zero {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths) :
    liveDescriptorData (A := A) p X hG hK active s repairLiveMode w (.base 9) =
      binSyms w.coordinateBits 0 := rfl

theorem selectedSourceBase_rho {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths) :
    liveDescriptorData (A := A) p X hG hK active s repairLiveMode w (.base 0) =
      binSyms w.coordinateBits p.ρ := rfl

theorem selectedSourceStride {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths) :
    liveDescriptorData (A := A) p X hG hK active s repairLiveMode w (.stride 1) =
      binSyms w.strideBits p.K := rfl

end
end IntegerMultBounds.MathlibTM2.Routing
