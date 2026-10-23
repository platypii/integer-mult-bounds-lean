module

public import IntegerMultBounds.MathlibTM2.Routing.RepairInactiveProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorData

/-! Inactive profile generation shares the live selector width and writes one
profile input; the count operand and six work tapes live outside the bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev liveInactiveProfileT (N J : ℕ) := liveDescriptorT N J + 7

def liveInactiveProfileCore {N J : ℕ} (i : Fin (liveDescriptorT N J)) : Fin (liveInactiveProfileT N J) :=
  Fin.castAdd 7 i

def liveInactiveProfileAux {N J : ℕ} (i : Fin 7) : Fin (liveInactiveProfileT N J) :=
  Fin.natAdd (liveDescriptorT N J) i

theorem liveInactiveProfileCore_injective {N J : ℕ} :
    Function.Injective (liveInactiveProfileCore (N := N) (J := J)) := Fin.castAdd_injective _ _

theorem liveInactiveProfileCore_aux {N J : ℕ} (i : Fin (liveDescriptorT N J)) (k : Fin 7) :
    liveInactiveProfileCore i ≠ liveInactiveProfileAux k := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [liveInactiveProfileCore, liveInactiveProfileAux] at hv
  omega

theorem liveInactiveProfileAux_injective {N J : ℕ} :
    Function.Injective (liveInactiveProfileAux (N := N) (J := J)) := by
  intro i k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [liveInactiveProfileAux] at hv
  omega

theorem liveInactiveProfileAux_core {N J : ℕ} (k : Fin 7) (i : Fin (liveDescriptorT N J)) :
    liveInactiveProfileAux k ≠ liveInactiveProfileCore i := (liveInactiveProfileCore_aux i k).symm

def liveInactiveProfileReg {N J : ℕ} (j : Fin J) : Fin 9 → Fin (liveInactiveProfileT N J) :=
  ![liveInactiveProfileCore (liveDescriptorAux .selectorBits), liveInactiveProfileAux 0,
    liveInactiveProfileAux 1, liveInactiveProfileCore (liveDescriptorAux (.input j)),
    liveInactiveProfileAux 2, liveInactiveProfileAux 3, liveInactiveProfileAux 4,
    liveInactiveProfileAux 5, liveInactiveProfileAux 6]

theorem liveInactiveProfileReg_injective {N J : ℕ} (j : Fin J) :
    Function.Injective (liveInactiveProfileReg (N := N) j) := by
  intro i k h
  fin_cases i <;> fin_cases k <;>
    simp_all [liveInactiveProfileReg, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff, liveInactiveProfileCore_aux,
      liveInactiveProfileAux_core, liveInactiveProfileAux_injective.eq_iff]

end
end IntegerMultBounds.MathlibTM2.Routing
