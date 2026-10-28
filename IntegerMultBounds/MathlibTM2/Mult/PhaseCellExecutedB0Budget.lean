module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedInverseBudget

/-! A concrete linear target precision meets the normalized inverse interface's smallness gate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem executedInverse_normalized_smallness {p : ℕ} (hp : 4 ≤ p) :
    2*(1/(2 : ℝ)^(p+8))+2/(2 : ℝ)^p+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2 ≤ 1/2 := by
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
  have hpSquare := pow_le_pow_left₀ (Nat.cast_nonneg p) hpPow 2
  have hpow : (2 : ℝ)^(p*2+6) ≤ (2 : ℝ)^(45*p) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hmatrix : 64*(p : ℝ)^2 ≤ (2 : ℝ)^(45*p) := by
    calc
      _ ≤ 64*((2 : ℝ)^p)^2 := mul_le_mul_of_nonneg_left hpSquare (by norm_num)
      _ = (2 : ℝ)^(p*2+6) := by rw [pow_add,pow_mul]; norm_num; ring
      _ ≤ _ := hpow
  have hden : (16 : ℝ) ≤ (2 : ℝ)^p := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp using 1 <;> norm_num
  have hquarter : 4/(2 : ℝ)^p ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    norm_num
    exact hden
  have hround : 1/(2 : ℝ)^(p+8) ≤ 1/(2 : ℝ)^p := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show p ≤ p+8 by omega)
  have hsolver : 2*(1/(2 : ℝ)^(p+8))+2/(2 : ℝ)^p ≤ 1/4 := by
    calc
      _ ≤ 2*(1/(2 : ℝ)^p)+2/(2 : ℝ)^p := add_le_add_left (mul_le_mul_of_nonneg_left hround (by norm_num : (0 : ℝ) ≤ 2)) _
      _ = 4/(2 : ℝ)^p := by ring
      _ ≤ 1/4 := hquarter
  have hperturb : (32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2 ≤ 1/4 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(45*p))).mpr
    nlinarith only [hmatrix]
  linarith only [hsolver,hperturb]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
