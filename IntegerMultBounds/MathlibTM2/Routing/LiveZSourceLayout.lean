module

public import IntegerMultBounds.MathlibTM2.Routing.RepairZSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveInactiveProfiles

/-! Z profile generation borrows the live control stride and row count as
its affine operands. Activity and restoration use the existing outer tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

def liveZSourceRole : Fin 12 → LiveDescriptorRole 11 :=
  ![.profile (.coordinate (.arithmetic .index)), .stride 5, .rows 5,
    .profile (.coordinate (.arithmetic .product)), .profile (.coordinate .wire), .profile .activity,
    .profile (.coordinate (.arithmetic .muls)), .profile (.coordinate (.arithmetic .mult)),
    .profile (.coordinate (.arithmetic .tx)), .profile (.coordinate (.arithmetic .ty)),
    .profile (.coordinate (.arithmetic .tz)), .profile .loadTmp]

def liveZSourceReg : Fin 12 → Fin (liveInactiveProfileT repairT 11) :=
  fun r => liveInactiveProfileCore (liveDescriptorAux (liveZSourceRole r))

theorem liveZSourceReg_injective : Function.Injective liveZSourceReg := by
  intro i j h
  have he := liveDescriptorAux_injective (liveInactiveProfileCore_injective h)
  fin_cases i <;> fin_cases j <;> simp_all [liveZSourceRole]

theorem liveZSourceAux_separate (i : Fin 7) (r : Fin 12) : liveInactiveProfileAux i ≠ liveZSourceReg r :=
  liveInactiveProfileAux_core _ _

def liveZSourceDst : Fin (liveInactiveProfileT repairT 11) := liveInactiveProfileCore (liveDescriptorAux (.input 3))

theorem liveZSourceDst_separate (r : Fin 12) : liveZSourceDst ≠ liveZSourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveZSourceRole]

def liveZSourceZeroRole : BinaryZeroReg → LiveDescriptorRole 11
  | .width => .selectorBits
  | .dst => .profile .activity
  | r => .zero r

def liveZSourceZeroReg : BinaryZeroReg → Fin (liveInactiveProfileT repairT 11) :=
  fun r => liveInactiveProfileCore (liveDescriptorAux (liveZSourceZeroRole r))

theorem liveZSourceZeroReg_injective : Function.Injective liveZSourceZeroReg := by
  intro i j h
  have he := liveDescriptorAux_injective (liveInactiveProfileCore_injective h)
  cases i <;> cases j <;> simp_all [liveZSourceZeroRole]

theorem liveZSourceZeroReg_dst : liveZSourceZeroReg .dst = liveZSourceReg 5 := rfl

theorem liveZSourceZeroReg_index (r : BinaryZeroReg) : liveZSourceZeroReg r ≠ liveZSourceReg 0 := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  cases r <;> simp [liveZSourceZeroRole, liveZSourceRole]

theorem liveZSourceAux_zero (i : Fin 7) (r : BinaryZeroReg) :
    liveInactiveProfileAux i ≠ liveZSourceZeroReg r := liveInactiveProfileAux_core _ _

def liveZSourceActivity (i : Fin repairT) : Fin (liveInactiveProfileT repairT 11) :=
  liveInactiveProfileCore (liveDescriptorCore i)

theorem liveZSourceActivity_aux (i : Fin repairT) (r : Fin 7) :
    liveZSourceActivity i ≠ liveInactiveProfileAux r := liveInactiveProfileCore_aux _ _

theorem liveZSourceActivity_reg (i : Fin repairT) (r : Fin 12) :
    liveZSourceActivity i ≠ liveZSourceReg r :=
  liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i _)

theorem liveZSourceActivity_zero (i : Fin repairT) (r : BinaryZeroReg) :
    liveZSourceActivity i ≠ liveZSourceZeroReg r :=
  liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i _)

theorem liveZSourceActivity_dst (i : Fin repairT) : liveZSourceActivity i ≠ liveZSourceDst :=
  liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i _)

end
end IntegerMultBounds.MathlibTM2.Routing
