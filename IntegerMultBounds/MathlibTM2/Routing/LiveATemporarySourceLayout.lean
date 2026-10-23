module

public import IntegerMultBounds.MathlibTM2.Routing.RepairATemporarySourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveYSourceLayout

/-! The temporary A source profile uses the existing full-width zero cursor
and control-row count. Five core scratch tapes suffice for direct enumeration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
noncomputable section

def liveATemporarySourceRole : Fin 5 → LiveDescriptorRole 11 :=
  ![.coordinate .cursor, .profile .activity, .profile (.coordinate (.arithmetic .tx)),
    .profile (.coordinate (.arithmetic .ty)), .profile .loadTmp]

def liveATemporarySourceReg : Fin 5 → Fin (liveInactiveProfileT repairT 11) :=
  fun r => liveInactiveProfileCore (liveDescriptorAux (liveATemporarySourceRole r))

theorem liveATemporarySourceReg_injective : Function.Injective liveATemporarySourceReg := by
  intro i j h
  have he := liveDescriptorAux_injective (liveInactiveProfileCore_injective h)
  fin_cases i <;> fin_cases j <;> simp_all [liveATemporarySourceRole]

def liveATemporarySourceCount : Fin (liveInactiveProfileT repairT 11) :=
  liveInactiveProfileCore (liveDescriptorAux (.rows 5))

def liveATemporarySourceDst : Fin (liveInactiveProfileT repairT 11) :=
  liveInactiveProfileCore (liveDescriptorAux (.input 2))

theorem liveATemporarySourceCount_separate (r : Fin 5) : liveATemporarySourceCount ≠ liveATemporarySourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveATemporarySourceRole]

theorem liveATemporarySourceDst_separate (r : Fin 5) : liveATemporarySourceDst ≠ liveATemporarySourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveATemporarySourceRole]

end
end IntegerMultBounds.MathlibTM2.Routing
