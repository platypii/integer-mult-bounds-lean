module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedError

/-! Select the normalization magnitude allowance from the stable inverse bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem inverse_round_magnitude (p target : ℕ) (y x : ℂ)
    (hx : ‖x‖ ≤ 64*(p : ℝ)) (he : ‖y-x‖ ≤ 1/(2 : ℝ)^target) :
    ‖y‖ ≤ 8*(2 : ℝ)^(p+8) := by
  apply computed_solution_norm target (p+8) y x _ he
  have hp : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
  have hpow : (2 : ℝ)^(p+8) = 256*(2 : ℝ)^p := by rw [pow_add]; norm_num; ring
  rw [hpow]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
