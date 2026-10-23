module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.InactiveClassifierBank

/-! Placement and classifier-generated repair share only their record stream.
All sixteen classifier workspace tapes are disjoint from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev inactiveClassifierPlacementT (t₀ : ℕ) := sharedScheduleT inactiveClassifierT t₀

def inactiveClassifierPlacementEmbed {t₀ : ℕ} : Fin inactiveClassifierT → Fin (inactiveClassifierPlacementT t₀) := sharedCoreEmbed

def inactiveClassifierPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (inactiveClassifierPlacementT t₀) :=
  sharedScheduleSlot (classifierCore (inactiveConfigurationCore repairHost.src))

theorem inactiveClassifierPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (inactiveClassifierPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem inactiveClassifierPlacementSlot_injective {t₀ : ℕ} : Function.Injective (inactiveClassifierPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (classifierCore (inactiveConfigurationCore repairHost.src))

@[simp] theorem inactiveClassifierPlacementSlot_str {t₀ : ℕ} :
    inactiveClassifierPlacementSlot (t₀ := t₀) .str = inactiveClassifierPlacementEmbed (classifierCore (inactiveConfigurationCore repairHost.src)) :=
  sharedScheduleSlot_str _

theorem inactiveClassifierPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin inactiveClassifierT) : inactiveClassifierPlacementSlot r ≠ inactiveClassifierPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem inactiveClassifierPlacementAux_separate {t₀ : ℕ} (i : Fin 16) (r : BinaryScheduleReg t₀ 3) :
    inactiveClassifierPlacementEmbed (classifierAux i) ≠ inactiveClassifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact (classifierCore_aux (inactiveConfigurationCore repairHost.src) i).symm

theorem inactiveClassifierPlacementConfiguration_separate {t₀ : ℕ} (i : Fin inactiveProfileConfigurationT)
    (hi : i ≠ inactiveConfigurationCore repairHost.src) (r : BinaryScheduleReg t₀ 3) :
    inactiveClassifierPlacementEmbed (classifierCore i) ≠ inactiveClassifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact classifierCore_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
