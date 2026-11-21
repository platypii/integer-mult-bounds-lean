module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIncoming
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryEntry

/-! Use the generated stage archive in place during the incoming directory pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)

/-- Extend the setup bank with six unused private caller tapes. The swap
workspace then starts immediately after the setup bank. -/
def ordinaryPackingSlot (i : Fin 64) : Fin (66+58) :=
  if h : i.val < 58 then entrySlot ⟨i.val,h⟩ else i.castLE (by decide)

def ordinaryPackingBank {K : ℕ} (room : 58 ≤ K) : Fin 64 ↪ Fin (66+K) :=
  (⟨ordinaryPackingSlot,by decide +kernel⟩ : Fin 64 ↪ Fin (66+58)).trans
    (Fin.castLEEmb (Nat.add_le_add_left room 66))

theorem ordinaryPackingBank_entry {K : ℕ} (room : 58 ≤ K) :
    (Fin.castLEEmb (by decide : 58 ≤ 64)).trans (ordinaryPackingBank room) = ordinaryCaller room := by
  ext i
  simp [ordinaryPackingBank,ordinaryPackingSlot,ordinaryCaller,entrySlots,Fin.isLt]

noncomputable def ordinaryPackingWork [M8.Machine.Net] {K : ℕ} (room : 58+(rowSwapBlock.tapes+35+1) ≤ K) :
    Fin (rowSwapBlock.tapes+35+1) ↪ Fin (66+K) :=
  (Fin.natAddEmb (66+58)).trans (Fin.castLEEmb (by omega))

theorem ordinaryPackingWork_apart [M8.Machine.Net] {K : ℕ} (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
    (i j) : ordinaryPackingWork room i ≠ ordinaryPackingBank (by omega : 58 ≤ K) j := by
  intro eq
  have val := congrArg Fin.val eq
  change 124+i.val = (ordinaryPackingSlot j).val at val
  have bound := (ordinaryPackingSlot j).isLt
  omega

/-- Translate the incoming pass's frame back to the public directory slots.
Slot 55 holds the parent weights at setup-bank index 48. -/
theorem ordinaryPacking_publicFrame [M8.Machine.Net] {K : ℕ} (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
    (S D : Stacks (66+K) prime) :
    let bank := ordinaryPackingBank (by omega : 58 ≤ K)
    let work := ordinaryPackingWork room
    let ports := columnPorts.trans (correctionColumnPlacement bank work (ordinaryPackingWork_apart room))
    (∀ j : Fin 64, 29 ≤ j.val → (∀ k, correctionCallerSlots k ≠ j) → D.R (bank j) = S.R (bank j)) →
    (∀ j, (∀ i, bank i ≠ j) → (∀ i, ports i ≠ j) → D.R j = S.R j) →
    ∀ j : Fin 64, 29 ≤ j.val → j.val < 58 → (∀ k, correctionCallerSlots k ≠ j) →
      D.R (j.castLE (by omega)) = S.R (j.castLE (by omega)) := by
  intro bank work ports kept outside j lo hi off
  by_cases weight : j = 55
  · subst j
    exact kept 48 (by decide) (by decide)
  have disjoint : ∀ i, bank i ≠ j.castLE (by omega) := by
    intro i eq
    have val := congrArg Fin.val eq
    change (ordinaryPackingSlot i).val = j.val at val
    exact (by decide +kernel : ∀ i j : Fin 64, 29 ≤ j.val → j.val < 58 → j ≠ 55 →
      (∀ k, correctionCallerSlots k ≠ j) → (ordinaryPackingSlot i).val ≠ j.val) i j lo hi weight off val
  apply outside _ disjoint
  intro i
  change sharedRegisterPlacement work (correctionCallerSlots.trans bank) correctionRole (columnPorts i) ≠ _
  cases h : correctionRole (columnPorts i) with
  | some k => simpa only [sharedRegisterPlacement,h,Function.Embedding.trans_apply] using disjoint (correctionCallerSlots k)
  | none =>
    simp only [sharedRegisterPlacement,h]
    intro eq
    have val := congrArg Fin.val eq
    change 124+(columnPorts i).val = j.val at val
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
