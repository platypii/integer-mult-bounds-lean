module

public import IntegerMultBounds.NLogN.Approx

/-! Error and magnitude bounds for the executed final normalization pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN

theorem computed_solution_norm (target E : ℕ) (y x : ℂ)
    (hx : ‖x‖ ≤ 4*(2 : ℝ)^E) (he : ‖y-x‖ ≤ 1/(2 : ℝ)^target) :
    ‖y‖ ≤ 8*(2 : ℝ)^E := by
  have hpow : (1 : ℝ) ≤ 2^E := one_le_pow₀ (by norm_num)
  have herr : 1/(2 : ℝ)^target ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have ht := norm_le_norm_sub_add y x
  linarith

theorem scaleRound_error (p j : ℕ) (y x : ℂ) (e : ℝ) (he : ‖y-x‖ ≤ e) :
    ‖rhoC p (((2 : ℂ)^j)⁻¹*y)-((2 : ℂ)^j)⁻¹*x‖ ≤ 2/(2 : ℝ)^p+e/(2 : ℝ)^j := by
  have hd : ‖((2 : ℂ)^j)⁻¹*y-((2 : ℂ)^j)⁻¹*x‖ ≤ e/(2 : ℝ)^j := by
    rw [←mul_sub,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2^j))
  calc
    _ = ‖(rhoC p (((2 : ℂ)^j)⁻¹*y)-((2 : ℂ)^j)⁻¹*y)+
        (((2 : ℂ)^j)⁻¹*y-((2 : ℂ)^j)⁻¹*x)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_rhoC_sub_le_two p _) hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
