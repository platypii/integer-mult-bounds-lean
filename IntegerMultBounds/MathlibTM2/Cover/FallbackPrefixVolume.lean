module

public import IntegerMultBounds.Networks.Shared50ModularControl
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A binary field pays for polynomial setup from one coordinate of its volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem cube_le_three_pow (a : ℕ) : a^3 ≤ 3^a := by
  induction a with
  | zero => decide
  | succ a ih =>
    match a with
    | 0 | 1 | 2 => decide
    | n+3 =>
      rw [pow_succ 3]
      apply le_trans _ (Nat.mul_le_mul_right 3 ih)
      ring_nf
      omega

/-- At binary field width, one remaining coordinate pays for the quadratic
bit-width overhead and the linear atom-width overhead of prefix enumeration. -/
theorem prefixSetup_volume_le (w d : ℕ) :
    let q := prime^(w+1)
    let H := Nat.size q
    (w+1+q^d)*(H+1)^2 ≤ (2*(Nat.size prime+1)^2)*q^(d+1) := by
  intro q H
  have bits : H ≤ (w+1)*Nat.size prime := by
    apply Nat.size_le.mpr
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (Nat.size_le.mp (le_refl (Nat.size prime))) (by omega)
  have field : H+1 ≤ (w+1)*(Nat.size prime+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have cube : (w+1)^3 ≤ prime^(w+1) := (cube_le_three_pow _).trans
    (Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_odd _)
  have prefixPos : 1 ≤ (prime^(w+1))^d := pow_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) _
  have factor : w+1+(prime^(w+1))^d ≤ 2*(w+1)*(prime^(w+1))^d := by
    nlinarith [Nat.mul_le_mul_left (w+1) prefixPos]
  change (w+1+(prime^(w+1))^d)*(H+1)^2 ≤ _
  grw [factor,field]
  calc
    _ = 2*(Nat.size prime+1)^2*q^d*(w+1)^3 := by dsimp only [q]; ring
    _ ≤ _ := by grw [cube]; rw [pow_succ q d]; dsimp only [q]; exact le_of_eq (by ring)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
