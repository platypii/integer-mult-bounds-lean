module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Dyadic rounding of disjoint publication windows, independent of machine
metadata, register layouts and numerical execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem pow_clog_two_le (k : ℕ) : 2^Nat.clog 2 k ≤ 2*k+1 := by
  by_cases hk : 1 < k
  · have ha := Nat.clog_pos (by decide : 1 < 2) hk
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hk
    have he : Nat.clog 2 k = (Nat.clog 2 k).pred+1 := (Nat.succ_pred_eq_of_pos ha).symm
    rw [he,pow_succ]
    omega
  · have he : k = 0 ∨ k = 1 := by omega
    rcases he with rfl | rfl <;> norm_num

/-- Rounding the number of disjoint equal-length windows costs at most a
constant factor, including the empty class. -/
theorem publicationPaddedVolume_le {s L : ℕ} (windows : PublicationWindows s L)
    (hL : L ≤ s) (b W : ℕ) :
    2^Nat.clog 2 windows.origins.length*2^b*(L*W) ≤ 3*(2^b*(s*W)) := by
  have hv := windows.gaps_volume 1
  simp only [scatterVolume,PublicationWindows.gaps_length,Nat.mul_one] at hv
  have hround := pow_clog_two_le windows.origins.length
  have hrows : windows.origins.length*L ≤ s := by omega
  have hpadded : 2^Nat.clog 2 windows.origins.length*L ≤ 3*s := by
    nlinarith only [Nat.mul_le_mul_right L hround,hrows,hL]
  have hh := Nat.mul_le_mul_right (2^b*W) hpadded
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

end IntegerMultBounds.MathlibTM2.Cost
