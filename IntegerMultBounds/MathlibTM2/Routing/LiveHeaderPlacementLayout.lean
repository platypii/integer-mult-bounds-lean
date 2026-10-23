module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderInputFrame

/-! Placement shares only the record stream with header-generated repair.
The complete header workspace is separate from placement metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

abbrev liveHeaderPlacementT (t₀ : ℕ) := sharedScheduleT repairLiveHeaderT t₀

def liveHeaderPlacementEmbed {t₀ : ℕ} : Fin repairLiveHeaderT → Fin (liveHeaderPlacementT t₀) := sharedCoreEmbed

def liveHeaderPlacementSlot {t₀ : ℕ} : BinaryScheduleReg t₀ 3 → Fin (liveHeaderPlacementT t₀) :=
  sharedScheduleSlot (repairLiveHeaderRaw repairHost.src)

theorem liveHeaderPlacementEmbed_injective {t₀ : ℕ} : Function.Injective (liveHeaderPlacementEmbed (t₀ := t₀)) :=
  sharedCoreEmbed_injective

theorem liveHeaderPlacementSlot_injective {t₀ : ℕ} : Function.Injective (liveHeaderPlacementSlot (t₀ := t₀)) :=
  sharedScheduleSlot_injective (repairLiveHeaderRaw repairHost.src)

@[simp] theorem liveHeaderPlacementSlot_str {t₀ : ℕ} :
    liveHeaderPlacementSlot (t₀ := t₀) .str = liveHeaderPlacementEmbed (repairLiveHeaderRaw repairHost.src) :=
  sharedScheduleSlot_str _

theorem liveHeaderPlacementSlot_separate {t₀ : ℕ} (r : BinaryScheduleReg t₀ 3) (hr : r ≠ .str)
    (i : Fin repairLiveHeaderT) : liveHeaderPlacementSlot r ≠ liveHeaderPlacementEmbed i :=
  sharedScheduleSlot_separate _ r hr i

theorem liveHeaderPlacementWork_separate {t₀ : ℕ} (r : HeaderWorkRole) (j : BinaryScheduleReg t₀ 3) :
    liveHeaderPlacementEmbed (sharedHeaderWork r) ≠ liveHeaderPlacementSlot j := by
  apply sharedCoreEmbed_separate
  exact (sharedHeaderCore_work (liveDescriptorCore repairHost.src) r).symm

theorem liveHeaderPlacementRaw_separate {t₀ : ℕ} (i : Fin repairT) (hi : i ≠ repairHost.src)
    (r : BinaryScheduleReg t₀ 3) :
    liveHeaderPlacementEmbed (repairLiveHeaderRaw i) ≠ liveHeaderPlacementSlot r := by
  apply sharedCoreEmbed_separate
  exact repairLiveHeaderRaw_injective.ne hi

end
end IntegerMultBounds.MathlibTM2.Routing
