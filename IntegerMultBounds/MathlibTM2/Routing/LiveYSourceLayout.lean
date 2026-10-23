module

public import IntegerMultBounds.MathlibTM2.Routing.RepairYSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveInactiveProfiles

/-! Y profile generation reuses live arithmetic scratch and the existing
seven-tape profile workspace. Its destination is the actual fifth live input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

def liveYSourceRole : Fin 12 → LiveDescriptorRole 11 :=
  ![.profile (.coordinate (.arithmetic .index)), .stride 0, .base 0,
    .profile (.coordinate (.arithmetic .product)), .profile (.coordinate .wire), .profile .activity,
    .profile (.coordinate (.arithmetic .muls)), .profile (.coordinate (.arithmetic .mult)),
    .profile (.coordinate (.arithmetic .tx)), .profile (.coordinate (.arithmetic .ty)),
    .profile (.coordinate (.arithmetic .tz)), .profile .loadTmp]

def liveYSourceReg : Fin 12 → Fin (liveInactiveProfileT repairT 11) :=
  fun r => liveInactiveProfileCore (liveDescriptorAux (liveYSourceRole r))

theorem liveYSourceReg_injective : Function.Injective liveYSourceReg := by
  intro i j h
  have he := liveDescriptorAux_injective (liveInactiveProfileCore_injective h)
  fin_cases i <;> fin_cases j <;> simp_all [liveYSourceRole]

theorem liveYSourceAux_separate (i : Fin 7) (r : Fin 12) : liveInactiveProfileAux i ≠ liveYSourceReg r :=
  liveInactiveProfileAux_core _ _

def liveYSourceDst : Fin (liveInactiveProfileT repairT 11) := liveInactiveProfileCore (liveDescriptorAux (.input 5))

theorem liveYSourceDst_separate (r : Fin 12) : liveYSourceDst ≠ liveYSourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveYSourceRole]

end
end IntegerMultBounds.MathlibTM2.Routing
