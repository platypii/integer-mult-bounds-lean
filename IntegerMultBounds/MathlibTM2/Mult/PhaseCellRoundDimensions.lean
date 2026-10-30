module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInversePrecisionSetup

/-! Pure normalization dimensions, independent of numerical dispatcher execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN

/-- The bit length of `4p` is a sufficient logarithmic normalization shift. -/
def inverseNormalizationShift (p : ℕ) : ℕ := Nat.size (4*p)

theorem inverseNormalizationShift_le (p : ℕ) : inverseNormalizationShift p ≤ p+2 := by
  apply Nat.size_le.mpr
  have h := Nat.mul_lt_mul_of_pos_left (show p < 2^p from Nat.lt_two_pow_self) (by omega : 0 < 4)
  simpa [pow_add,Nat.mul_comm] using h

theorem inverseNormalizationShift_large (p : ℕ) : 4*(p : ℝ) ≤ (2 : ℝ)^inverseNormalizationShift p := by
  have h : 4*p < 2^Nat.size (4*p) := Nat.size_le.mp (le_refl _)
  exact_mod_cast h.le

theorem inverse_round_dimensions (p l target rowCount band j : ℕ) (hj : j ≤ p+2) :
    let E := inverseExecutionExponent p l target rowCount band
    p ≤ 4*E ∧ 4*E+(p+8)+5 ≤ 8*E+8 ∧
      4*E-p+j+(p+(p+8)+5) ≤ 8*E+8 := by
  dsimp [inverseExecutionExponent]
  omega


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
