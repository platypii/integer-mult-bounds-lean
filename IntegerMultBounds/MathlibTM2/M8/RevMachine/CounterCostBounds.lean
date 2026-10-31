module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Counters

/-! Structural runtime bounds for counter advances, shared by time and
workspace proofs without importing the recursive family budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget
open IntegerMultBounds.Machine FlatCoordinateSchedule

theorem bits_len (x : ℕ) : (bits x).length ≤ x + 1 := by
  have := Headers.length_le (bits x) (FlatCoordinateSchedule.bits_canonical x)
  rwa [FlatCoordinateSchedule.bits_value] at this

theorem advsCost_le (X Y : ℕ) : ∀ r, Counters.advsCost X Y r ≤
    (r + 1) * (10 * Y + 2 * (X + (r + 1) * Y + 1) + 7 * (Y + 1) + 29)
  | 0 => by
    have := bits_len X; have := bits_len Y
    simp only [Counters.advsCost, Counters.advCost]; omega
  | r+1 => by
    have ih := advsCost_le X Y r
    have h1 := bits_len (X + (r + 1) * Y); have h2 := bits_len Y
    simp only [Counters.advsCost, Counters.advCost]
    nlinarith

theorem advs_le {Y M r m : ℕ} (hY : Y ≤ M) (hM : 1 ≤ M) (hr : r + 1 ≤ m + 1) :
    Counters.advsCost 0 Y r ≤ (m + 1) * ((2 * m + 57) * M) := by
  refine (advsCost_le 0 Y r).trans (Nat.mul_le_mul hr ?_)
  have e1 : (r + 1) * Y ≤ m * M + M := by
    have h := Nat.mul_le_mul hr hY
    calc (r + 1) * Y ≤ (m + 1) * M := h
      _ = m * M + M := by ring
  have e2 : (2 * m + 57) * M = 2 * (m * M) + 57 * M := by ring
  rw [e2]
  omega

end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget
