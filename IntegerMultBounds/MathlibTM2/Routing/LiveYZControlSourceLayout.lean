module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYZControlOffset
public import IntegerMultBounds.MathlibTM2.Routing.RepairYZControlSourceGenerate

/-! Reuse the first-Z arithmetic layout, with the computed YZ base on outer
tape six and the actual second-YZ profile as destination. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
noncomputable section

local notation "T₀" => liveInactiveProfileT repairT 11

def liveYZControlSourceReg : Fin 12 → Fin T₀ :=
  Function.update liveZSourceReg 2 (liveInactiveProfileAux 6)

theorem liveYZControlSourceReg_injective : Function.Injective liveYZControlSourceReg := by
  intro i j h
  by_cases hi : i = 2
  · subst i
    by_cases hj : j = 2
    · exact hj.symm
    · simp only [liveYZControlSourceReg, Function.update_self, Function.update_of_ne hj] at h
      exact (liveZSourceAux_separate 6 j h).elim
  · by_cases hj : j = 2
    · subst j
      simp only [liveYZControlSourceReg, Function.update_self, Function.update_of_ne hi] at h
      exact (liveZSourceAux_separate 6 i h.symm).elim
    · simp only [liveYZControlSourceReg, Function.update_of_ne hi, Function.update_of_ne hj] at h
      exact liveZSourceReg_injective h

theorem liveYZControlSourceAux_separate (i : Fin 7) (hi : i ≠ 6) (r : Fin 12) :
    liveInactiveProfileAux i ≠ liveYZControlSourceReg r := by
  by_cases hr : r = 2
  · subst r
    dsimp only [liveYZControlSourceReg, Function.update_self]
    exact liveInactiveProfileAux_injective.ne hi
  · simpa only [liveYZControlSourceReg, Function.update_of_ne hr] using liveZSourceAux_separate i r

theorem liveYZControlSourceActivity_reg (i : Fin repairT) (r : Fin 12) :
    liveZSourceActivity i ≠ liveYZControlSourceReg r := by
  by_cases hr : r = 2
  · subst r
    exact liveZSourceActivity_aux i 6
  · simpa only [liveYZControlSourceReg, Function.update_of_ne hr] using liveZSourceActivity_reg i r

def liveYZControlSourceDst : Fin T₀ := liveInactiveProfileCore (liveDescriptorAux (.input 8))

theorem liveYZControlSourceDst_separate (r : Fin 12) : liveYZControlSourceDst ≠ liveYZControlSourceReg r := by
  by_cases hr : r = 2
  · subst r
    exact liveInactiveProfileCore_aux _ _
  · simp only [liveYZControlSourceReg, Function.update_of_ne hr]
    apply liveInactiveProfileCore_injective.ne
    apply liveDescriptorAux_injective.ne
    fin_cases r <;> simp [liveZSourceRole]

end
end IntegerMultBounds.MathlibTM2.Routing
