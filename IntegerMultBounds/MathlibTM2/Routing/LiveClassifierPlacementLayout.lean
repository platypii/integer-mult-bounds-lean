module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.LiveClassifierBank

/-! Placement and classifier-generated repair share only their record stream.
All sixteen classifier workspace tapes are disjoint from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev liveClassifierPlacementT (t₀ : ℕ) := sharedScheduleT liveClassifierT t₀

def liveClassifierPlacementEmbed {t₀ : ℕ} : Fin liveClassifierT → Fin (liveClassifierPlacementT t₀) := sharedCoreEmbed

def liveClassifierPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (liveClassifierPlacementT t₀) :=
  sharedScheduleSlot (classifierCore (liveHeaderConfigurationCore repairHost.src))

theorem liveClassifierPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (liveClassifierPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem liveClassifierPlacementSlot_injective {t₀ : ℕ} : Function.Injective (liveClassifierPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (classifierCore (liveHeaderConfigurationCore repairHost.src))

@[simp] theorem liveClassifierPlacementSlot_str {t₀ : ℕ} :
    liveClassifierPlacementSlot (t₀ := t₀) .str = liveClassifierPlacementEmbed (classifierCore (liveHeaderConfigurationCore repairHost.src)) :=
  sharedScheduleSlot_str _

theorem liveClassifierPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin liveClassifierT) : liveClassifierPlacementSlot r ≠ liveClassifierPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem liveClassifierPlacementAux_separate {t₀ : ℕ} (i : Fin 16) (r : BinaryScheduleReg t₀ 3) :
    liveClassifierPlacementEmbed (classifierAux i) ≠ liveClassifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact (classifierCore_aux (liveHeaderConfigurationCore repairHost.src) i).symm

theorem liveClassifierPlacementConfiguration_separate {t₀ : ℕ} (i : Fin liveHeaderConfigurationT)
    (hi : i ≠ liveHeaderConfigurationCore repairHost.src) (r : BinaryScheduleReg t₀ 3) :
    liveClassifierPlacementEmbed (classifierCore i) ≠ liveClassifierPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact classifierCore_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
