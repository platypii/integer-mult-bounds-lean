module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscale

/-! Propagate retained-residual error through normalization and exact unscaling. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Normalization adds one truncation error to the scaled retained-residual error. -/
theorem boundary_normalized_rhs_error (q E e : ℕ) (hq : q = E+e+1)
    (z : GaussianInt) (c : ℂ) (δ : ℝ) (hz : ‖value q z - c‖ ≤ δ) :
    ‖value q (normalizeBoundaryWord q e z) - c/(2 : ℂ)^(E+1)‖ ≤
      2/(2 : ℝ)^q + δ/(2 : ℝ)^(E+1) := by
  have hnorm : ‖(2 : ℂ)^(E+1)‖ = (2 : ℝ)^(E+1) := by norm_num [norm_pow]
  calc
    _ ≤ ‖value q (normalizeBoundaryWord q e z) - value q z/(2 : ℂ)^(E+1)‖ +
        ‖value q z/(2 : ℂ)^(E+1) - c/(2 : ℂ)^(E+1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (normalizeBoundaryWord_scaled_error q E e hq z) (by
      rw [← sub_div,norm_div,hnorm]
      exact div_le_div_of_nonneg_right hz (by positivity))

/-- Exact unscaling multiplies the entire normalized error by the same power of two. -/
theorem boundary_unscaled_solution_error (q : ℕ) (z : GaussianInt) (x : ℂ)
    (ε : ℝ) (hz : ‖value q z - x/(2 : ℂ)^(q/2+1)‖ ≤ ε) :
    ‖value q (unscaleBoundaryWord q z) - x‖ ≤ (2 : ℝ)^(q/2+1)*ε := by
  have hnorm : ‖(2 : ℂ)^(q/2+1)‖ = (2 : ℝ)^(q/2+1) := by norm_num [norm_pow]
  have heq : value q (unscaleBoundaryWord q z) - x =
      (2 : ℂ)^(q/2+1)*(value q z - x/(2 : ℂ)^(q/2+1)) := by
    rw [unscaleBoundaryWord_value,mul_sub,mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
  rw [heq,norm_mul,hnorm]
  exact mul_le_mul_of_nonneg_left hz (by positivity)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
