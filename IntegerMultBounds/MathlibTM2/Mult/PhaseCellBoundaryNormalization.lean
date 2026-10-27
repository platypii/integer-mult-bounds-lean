module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream

/-! Normalize a residual of grid magnitude at most a power of two into the solve's half-unit disk. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The exact multiplier stream used for residual normalization. -/
def normalizeBoundaryWord (q e : ℕ) (z : GaussianInt) : GaussianInt :=
  tdivN q (z * ⟨(2 : ℤ)^e,0⟩)

theorem normalized_component_bound (q E e : ℕ) (hq : q = E+e+1) (z : ℤ)
    (hz : |gv q z| ≤ (2 : ℝ)^E) :
    |gv q ((z*(2 : ℤ)^e).tdiv (2^q))| ≤ 1/2 := by
  have h := abs_gv_tdiv q (z*(2 : ℤ)^e) q
  have he : gv q (z*(2 : ℤ)^e) = gv q z*(2 : ℝ)^e := by simp [gv]; ring
  rw [he,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < 2^e)] at h
  have hpow : (2 : ℝ)^q = (2 : ℝ)^E*(2 : ℝ)^e*2 := by rw [hq,pow_add,pow_add]; norm_num
  calc
    _ ≤ (|gv q z| * (2 : ℝ)^e)/(2 : ℝ)^q := h
    _ ≤ ((2 : ℝ)^E*(2 : ℝ)^e)/(2 : ℝ)^q := by gcongr
    _ = 1/2 := by rw [hpow]; field_simp

theorem normalizeBoundaryWord_bound (q E e : ℕ) (hq : q = E+e+1) (z : GaussianInt)
    (hz : |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E) :
    |gv q (normalizeBoundaryWord q e z).re| ≤ 1/2 ∧
      |gv q (normalizeBoundaryWord q e z).im| ≤ 1/2 := by
  constructor
  · simpa [normalizeBoundaryWord,tdivN,mul_real_re] using normalized_component_bound q E e hq z.re hz.1
  · simpa [normalizeBoundaryWord,tdivN,mul_real_im] using normalized_component_bound q E e hq z.im hz.2

/-- The wide execution word accommodates the unnormalized residual as well as its scalar. -/
theorem boundary_normalization_fits (q E e : ℕ) (hq : q = E+e+1) (z : GaussianInt)
    (hz : |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E) :
    Fits (2*q+8) z ∧ Fits (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt) ∧
      Fits (2*q+8) (normalizeBoundaryWord q e z) := by
  have hEq : E ≤ q := by omega
  have heq : e ≤ q := by omega
  have hpow : (2 : ℝ)^q*(2 : ℝ)^q < (2 : ℝ)^(2*q+8-1) := by
    rw [←pow_add]
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  have hqpos : (0 : ℝ) < 2^q := by positivity
  have hone : (1 : ℝ) ≤ 2^q := one_le_pow₀ (by norm_num)
  have hC : (2 : ℝ)^E ≤ (2 : ℝ)^q := pow_le_pow_right₀ (by norm_num) hEq
  have hscalar : |gv q ((2 : ℤ)^e)| ≤ (2 : ℝ)^q := by
    have he : (2 : ℝ)^e ≤ (2 : ℝ)^q := pow_le_pow_right₀ (by norm_num) heq
    simp only [gv,Int.cast_pow,Int.cast_ofNat,abs_div,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
    apply (div_le_iff₀ hqpos).mpr
    exact he.trans (le_mul_of_one_le_right (by positivity) hone)
  have hbound := normalizeBoundaryWord_bound q E e hq z hz
  refine ⟨fitsC_of_gv (hz.1.trans hC) (hz.2.trans hC) hpow,
    fitsC_of_gv hscalar ?_ hpow,fitsC_of_gv (hbound.1.trans ?_) (hbound.2.trans ?_) hpow⟩
  · simp only [gv_zero,abs_zero]; positivity
  · linarith
  · linarith

theorem boundary_normalization_scalar_value (q E e : ℕ) (hq : q = E+e+1) :
    value q (⟨(2 : ℤ)^e,0⟩ : GaussianInt) = ((1/(2 : ℝ)^(E+1) : ℝ) : ℂ) := by
  rw [value_real]
  apply congrArg (fun x : ℝ => (x : ℂ))
  simp only [Int.cast_pow,Int.cast_ofNat]
  have hpow : (2 : ℝ)^q = (2 : ℝ)^e*(2 : ℝ)^(E+1) := by
    rw [hq,show E+e+1 = e+(E+1) by omega,pow_add]
  rw [hpow]
  field_simp

theorem normalizeBoundaryWord_error (q e : ℕ) (z : GaussianInt) :
    ‖value q (normalizeBoundaryWord q e z)-value q z*value q (⟨(2 : ℤ)^e,0⟩ : GaussianInt)‖ ≤
      2/(2 : ℝ)^q := realScalar_error q z _

theorem normalizeBoundaryWord_scaled_error (q E e : ℕ) (hq : q = E+e+1) (z : GaussianInt) :
    ‖value q (normalizeBoundaryWord q e z)-value q z/(2 : ℂ)^(E+1)‖ ≤ 2/(2 : ℝ)^q := by
  have h := normalizeBoundaryWord_error q e z
  rw [boundary_normalization_scalar_value q E e hq] at h
  simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_ofNat,mul_one_div] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
