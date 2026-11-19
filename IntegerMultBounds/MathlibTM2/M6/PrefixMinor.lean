module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Heights
public import IntegerMultBounds.Networks.Shared50ModularControl
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.Int.Basic

/-! Nonzero prefix minors of the translated PR589 generators survive at every tape radix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks Shared50ModularControl

/-- Every nonzero integer of at most this magnitude is a unit at every tape radix. -/
theorem prefix_denominator_unit (den : ℤ) (nz : den ≠ 0) (bound : den.natAbs ≤ 2 ^ 100)
    (w : ℕ) : IsUnit (den : ZMod (prime ^ w)) := by
  have expBound : 100 ≤ coefficientExponent := by
    apply le_coefficientExponent
    calc 100 ≤ 2 ^ 7 := by decide
         _ ≤ 2 ^ 53000 := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 7 ≤ 53000)
  have small := bound.trans_lt ((two_pow_le_coefficientBound expBound).trans_lt coefficientBound_lt_prime)
  have coprime := (Nat.coprime_of_lt_prime (Int.natAbs_ne_zero.mpr nz)
    small prime_prime).symm
  exact (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa using (coprime.pow_right w).symm))

theorem prefix_det_bound {d : ℕ} (dim : d ≤ 8) (A : Matrix (Fin d) (Fin d) ℤ)
    (entries : ∀ i j, (A i j).natAbs ≤ 1344) : A.det.natAbs ≤ 2 ^ 100 := by
  calc
    A.det.natAbs ≤ d.factorial * 1344 ^ d := M8.Rev.natAbs_det_le entries
    _ ≤ Nat.factorial 8 * 1344 ^ 8 :=
      Nat.mul_le_mul (Nat.factorial_le dim) (Nat.pow_le_pow_right (by decide) dim)
    _ ≤ 2 ^ 100 := by decide

/-- The translated generators have entries of magnitude at most 1344. A nonsingular
prefix minor of these generators supplies an invertible matrix at every width. -/
theorem prefix_minor_unit {d : ℕ} (dim : d ≤ 8) (A : Matrix (Fin d) (Fin d) ℤ)
    (entries : ∀ i j, (A i j).natAbs ≤ 1344) (nonsingular : A.det ≠ 0) (w : ℕ) :
    IsUnit (A.map (Int.castRingHom (ZMod (prime ^ w)))) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit (((Int.castRingHom (ZMod (prime ^ w))).mapMatrix A).det)
  rw [← RingHom.map_det]
  exact prefix_denominator_unit A.det nonsingular (prefix_det_bound dim A entries) w

end IntegerMultBounds.MathlibTM2.M6
