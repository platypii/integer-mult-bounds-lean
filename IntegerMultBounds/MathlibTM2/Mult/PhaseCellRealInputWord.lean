module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode
public import IntegerMultBounds.NLogN.Approx

/-! Real right-hand sides rounded toward zero to the actual Gaussian input grid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.ShortConv

noncomputable def realInputWord (q : ℕ) (x : ℝ) : GaussianInt := ⟨rho0 ((2 : ℝ)^q*x),0⟩

@[simp] theorem realInputWord_value_re (q : ℕ) (x : ℝ) :
    (value q (realInputWord q x)).re = (rho0 ((2 : ℝ)^q*x) : ℝ)/(2 : ℝ)^q := rfl

@[simp] theorem realInputWord_value_im (q : ℕ) (x : ℝ) : (value q (realInputWord q x)).im = 0 := by
  simp only [value,realInputWord,Int.cast_zero,zero_div]

theorem realInputWord_norm (q : ℕ) (x : ℝ) :
    ‖value q (realInputWord q x)‖ = |(value q (realInputWord q x)).re| := by
  have hv : value q (realInputWord q x) = ((value q (realInputWord q x)).re : ℂ) := by
    apply Complex.ext <;> simp only [realInputWord_value_im,Complex.ofReal_re,Complex.ofReal_im]
  conv_lhs => rw [hv,Complex.norm_real,Real.norm_eq_abs]

theorem realInputWord_norm_le (q : ℕ) (x : ℝ) : ‖value q (realInputWord q x)‖ ≤ |x| := by
  have hp : (0 : ℝ) < 2^q := by positivity
  rw [realInputWord_norm,realInputWord_value_re,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have h := abs_rho0_le ((2 : ℝ)^q*x)
  simpa only [abs_mul,abs_of_pos hp,mul_comm] using h

theorem realInputWord_error (q : ℕ) (x : ℝ) :
    |(value q (realInputWord q x)).re-x| ≤ 1/(2 : ℝ)^q := by
  have hp : (0 : ℝ) < 2^q := by positivity
  rw [realInputWord_value_re]
  have he : (rho0 ((2 : ℝ)^q*x) : ℝ)/(2 : ℝ)^q-x =
      ((rho0 ((2 : ℝ)^q*x) : ℝ)-(2 : ℝ)^q*x)/(2 : ℝ)^q := by field_simp
  rw [he,abs_div,abs_of_pos hp]
  exact (div_le_div_of_nonneg_right (abs_rho0_sub_lt _).le hp.le)

theorem realInputWord_grid (q : ℕ) (z : ℤ) : realInputWord q ((z : ℝ)/(2 : ℝ)^q) = ⟨z,0⟩ := by
  have he : (2 : ℝ)^q*((z : ℝ)/(2 : ℝ)^q) = z := by field_simp
  ext <;> simp only [realInputWord,he]
  unfold rho0
  split_ifs <;> simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
