module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandValue

/-! # Exact integer arithmetic for chirp output scaling

The ring numerator is at precision q+1 with correlation scale 4*2^l. Shifting its
numerator by l+1 restores the correlation at precision q. Both real products then
round on that same q-grid, matching the analytic output formula exactly.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- A numerator shift is exact multiplication of the decoded value. -/
theorem value_pow_two_mul (p d : ℕ) (z : GaussianInt) :
    value p ((2 : GaussianInt) ^ d * z) = (2 : ℂ) ^ d * value p z := by
  rw [value_eq_grid, value_eq_grid, map_mul, map_pow]
  rw [show GaussianInt.toComplex (2 : GaussianInt) = (2 : ℂ) from map_natCast _ 2]
  ring

/-- Truncating d numerator bits and lowering precision by d is exactly grid rounding. -/
theorem value_tdivN (p d : ℕ) (z : GaussianInt) :
    value p (tdivN d z) = rhoC p (value (p + d) z) := by
  have hscale (x : ℤ) : (2 : ℝ) ^ p * ((x : ℝ) / 2 ^ (p + d)) = (x : ℝ) / 2 ^ d := by
    rw [pow_add]
    field_simp
  apply Complex.ext
  · change ((z.re.tdiv (2 ^ d) : ℤ) : ℝ) / 2 ^ p =
      (rho0 (2 ^ p * ((z.re : ℝ) / 2 ^ (p + d))) : ℝ) / 2 ^ p
    rw [hscale, tdiv_rho0]
  · change ((z.im.tdiv (2 ^ d) : ℤ) : ℝ) / 2 ^ p =
      (rho0 (2 ^ p * ((z.im : ℝ) / 2 ^ (p + d))) : ℝ) / 2 ^ p
    rw [hscale, tdiv_rho0]

/-- The output machine can perform the final p-grid rounding by signed truncation. -/
theorem value_round_precision {p q : ℕ} (hpq : p ≤ q) (z : GaussianInt) :
    value p (tdivN (q - p) z) = rhoC p (value q z) := by
  rw [value_tdivN, Nat.add_sub_of_le hpq]

/-- Undo the ring product's correlation scale without changing fractional precision. -/
theorem value_chirp_correlation_scale (q l : ℕ) (z : GaussianInt) :
    value q ((2 : GaussianInt) ^ (l + 1) * z) =
      (4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) z := by
  rw [value_pow_two_mul, value_succ]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- Integer output numerator before the final p-grid rounding.
`e` represents the normalized E factor and `a` represents 1/(2α), both at precision q. -/
def chirpOutputNumerator (q l Γ : ℕ) (c : GaussianInt) (e a : ℤ) : GaussianInt :=
  tdivN q ((⟨a, 0⟩ : GaussianInt) * ((2 : GaussianInt) ^ Γ *
    tdivN q ((⟨e, 0⟩ : GaussianInt) * ((2 : GaussianInt) ^ (l + 1) * c))))

/-- Exact semantics of the two real products and both numerator shifts. -/
theorem value_chirpOutputNumerator (q l Γ : ℕ) (c : GaussianInt) (e a : ℤ) :
    value q (chirpOutputNumerator q l Γ c e a) =
      rhoC q ((((a : ℝ) / 2 ^ q : ℝ) : ℂ) * ((2 : ℂ) ^ Γ *
        rhoC q ((((e : ℝ) / 2 ^ q : ℝ) : ℂ) * ((4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) c)))) := by
  rw [chirpOutputNumerator, value_tdivN_mul, value_real, value_pow_two_mul,
    value_tdivN_mul, value_real, value_chirp_correlation_scale]

/-- The complete integer output formula includes the final grid rounding. -/
theorem value_chirpOutput {p q : ℕ} (hpq : p ≤ q) (l Γ : ℕ) (c : GaussianInt) (e a : ℤ) :
    value p (tdivN (q - p) (chirpOutputNumerator q l Γ c e a)) =
      rhoC p (rhoC q ((((a : ℝ) / 2 ^ q : ℝ) : ℂ) * ((2 : ℂ) ^ Γ *
        rhoC q ((((e : ℝ) / 2 ^ q : ℝ) : ℂ) * ((4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) c))))) := by
  rw [value_round_precision hpq, value_chirpOutputNumerator]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
