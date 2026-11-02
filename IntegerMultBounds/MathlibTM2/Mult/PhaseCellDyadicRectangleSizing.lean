module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Minimal dyadic rectangle capacities and a shared metadata word width.
Padding is per axis, independent of the other axis's radix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def dyadicCapacity (n : ℕ) : ℕ := 2^Nat.clog 2 n

theorem le_dyadicCapacity (n : ℕ) : n ≤ dyadicCapacity n := Nat.le_pow_clog (by decide) n

theorem dyadicCapacity_pos (n : ℕ) : 0 < dyadicCapacity n := Nat.two_pow_pos _

theorem dyadicCapacity_le_twice (n : ℕ) : dyadicCapacity n ≤ 2*max 1 n := by
  by_cases hn : n ≤ 1
  · simp [dyadicCapacity,Nat.clog_of_right_le_one hn,max_eq_left hn]
  · have hp := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n)
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < n)
    have he : Nat.clog 2 n = (Nat.clog 2 n).pred+1 := (Nat.succ_pred_eq_of_pos hp).symm
    rw [dyadicCapacity,he,pow_succ]
    omega

@[simp] theorem dyadicCapacity_pow (a : ℕ) : dyadicCapacity (2^a) = 2^a := by
  simp only [dyadicCapacity,Nat.clog_pow 2 a (by decide)]

theorem dyadicRectangleVolume_le (rows keys packet : ℕ) :
    dyadicCapacity rows*dyadicCapacity keys*packet ≤ 4*max 1 rows*max 1 keys*packet := by
  have hh := Nat.mul_le_mul (dyadicCapacity_le_twice rows) (dyadicCapacity_le_twice keys)
  have hm := Nat.mul_le_mul_right packet hh
  nlinarith only [hm]

theorem dyadicRectangleVolume_le_axis (rows keys axis packet : ℕ) (haxis : 0 < axis) (hkeys : keys ≤ axis) :
    dyadicCapacity rows*dyadicCapacity keys*packet ≤ 4*max 1 rows*axis*packet := by
  have hk : max 1 keys ≤ axis := by omega
  exact (dyadicRectangleVolume_le rows keys packet).trans
    (Nat.mul_le_mul_right packet (Nat.mul_le_mul_left (4*max 1 rows) hk))

def dyadicWordWidth (a b packet : ℕ) : ℕ := a+b+Nat.size packet

theorem dyadicWordWidth_gates (a b packet : ℕ) (hpacket : 0 < packet) :
    a+b < dyadicWordWidth a b packet ∧
      packet*2^(a+b) < 2^dyadicWordWidth a b packet ∧
      dyadicWordWidth a b packet ≤ 2^a*2^b*packet := by
  have hsize : 0 < Nat.size packet := Nat.size_pos.mpr hpacket
  have hfit := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self packet) (Nat.two_pow_pos (a+b))
  have hsizeLe : Nat.size packet ≤ packet := Nat.size_le.mpr Nat.lt_two_pow_self
  have hp : a+b+1 ≤ 2^(a+b) := Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul_left packet hp
  have hs : a+b ≤ packet*(a+b) := Nat.le_mul_of_pos_left _ hpacket
  refine ⟨by unfold dyadicWordWidth; omega,?_,?_⟩
  · simpa only [dyadicWordWidth,pow_add,Nat.mul_comm] using hfit
  · unfold dyadicWordWidth
    rw [←pow_add,Nat.mul_comm]
    nlinarith only [hsizeLe,hm,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
