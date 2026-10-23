module

public import IntegerMultBounds.MathlibTM2.Routing.RepairAControlSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveZSourceLayout

/-! First-A source generation shares the Z arithmetic layout. Group repetition
borrows three outer tapes and restored arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
noncomputable section
local notation "T₀" => liveInactiveProfileT repairT 11

def liveAControlRepeatReg : Fin 7 → Fin T₀ :=
  ![liveInactiveProfileCore (liveDescriptorAux .group), liveInactiveProfileAux 2,
    liveInactiveProfileAux 5, liveInactiveProfileAux 6, liveZSourceReg 3, liveZSourceReg 8, liveZSourceReg 9]

theorem liveAControlRepeatReg_injective : Function.Injective liveAControlRepeatReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [liveAControlRepeatReg, liveZSourceReg, liveZSourceRole,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileCore_aux, liveInactiveProfileAux_core]

theorem liveAControlRepeat_frame (r : Fin 7) : liveAControlRepeatReg r ≠ liveZSourceReg 5 := by
  fin_cases r <;> simp [liveAControlRepeatReg, liveZSourceReg, liveZSourceRole,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff, liveInactiveProfileAux_core]

theorem liveAControlRepeat_output (r : Fin 12) : liveAControlRepeatReg 3 ≠ liveZSourceReg r :=
  liveInactiveProfileAux_core _ _

theorem liveAControlRepeat_index (r : Fin 7) : liveAControlRepeatReg r ≠ liveZSourceReg 0 := by
  fin_cases r <;> simp [liveAControlRepeatReg, liveZSourceReg, liveZSourceRole,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff, liveInactiveProfileAux_core]

theorem liveAControlRepeat_activity (i : Fin repairT) (r : Fin 7) :
    liveZSourceActivity i ≠ liveAControlRepeatReg r := by
  fin_cases r <;> simp [liveAControlRepeatReg, liveZSourceReg, liveZSourceActivity,
    liveInactiveProfileCore_injective.eq_iff, liveDescriptorCore_aux, liveInactiveProfileCore_aux]

theorem liveAControlRepeat_aux (i : Fin 7) (h2 : i ≠ 2) (h5 : i ≠ 5) (h6 : i ≠ 6) (r : Fin 7) :
    liveInactiveProfileAux i ≠ liveAControlRepeatReg r := by
  fin_cases r <;> simp [liveAControlRepeatReg, liveZSourceReg, liveInactiveProfileAux_core,
    liveInactiveProfileAux_injective.eq_iff, h2, h5, h6]

def liveAControlSourceDst : Fin T₀ := liveInactiveProfileCore (liveDescriptorAux (.input 1))

theorem liveAControlSourceDst_separate (r : Fin 12) : liveAControlSourceDst ≠ liveZSourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveZSourceRole]

end
end IntegerMultBounds.MathlibTM2.Routing
