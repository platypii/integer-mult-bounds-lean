module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputValue

/-! Undo boundary normalization exactly, within the existing execution word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def unscaleBoundaryWord (q : ℕ) (z : GaussianInt) : GaussianInt :=
  z * ⟨(2 : ℤ)^(q/2+1),0⟩

theorem integer_unscale_exact (q m : ℕ) (a : ℤ) :
    (a*(2 : ℤ)^(q+m)).tdiv (2^q) = a*(2 : ℤ)^m := by
  rw [pow_add,show a*((2 : ℤ)^q*2^m) = (a*2^m)*2^q by ring]
  exact Int.mul_tdiv_cancel _ (by positivity)

theorem boundary_unscale_product (q : ℕ) (z : GaussianInt) :
    tdivN q (z * ⟨(2 : ℤ)^(q+q/2+1),0⟩) = unscaleBoundaryWord q z := by
  ext
  · simpa [tdivN,mul_real_re,unscaleBoundaryWord,Nat.add_assoc] using integer_unscale_exact q (q/2+1) z.re
  · simpa [tdivN,mul_real_im,unscaleBoundaryWord,Nat.add_assoc] using integer_unscale_exact q (q/2+1) z.im

theorem gaussian_two_pow_real (n : ℕ) : (2 : GaussianInt)^n = ⟨(2 : ℤ)^n,0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,ih]
    ext <;> simp [pow_succ]

theorem unscaleBoundaryWord_value (q : ℕ) (z : GaussianInt) :
    value q (unscaleBoundaryWord q z) = (2 : ℂ)^(q/2+1)*value q z := by
  rw [unscaleBoundaryWord,← gaussian_two_pow_real,mul_comm]
  exact value_pow_two_mul q (q/2+1) z

/-- The stored inverse-scale scalar fits without increasing the execution width. -/
theorem boundary_unscale_scalar_fits (q : ℕ) :
    Fits (2*q+8) (⟨(2 : ℤ)^(q+q/2+1),0⟩ : GaussianInt) := by
  constructor
  · change |(2 : ℤ)^(q+q/2+1)| < 2^(2*q+8-1)
    rw [abs_of_pos (by positivity : (0 : ℤ) < 2^(q+q/2+1))]
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  · change |(0 : ℤ)| < 2^(2*q+8-1)
    positivity

/-- Even the coarse half-unit-RHS solution bound fits after exact unscaling. -/
theorem boundary_unscale_fits (q p : ℕ) (hpq : p ≤ q/2) (z : GaussianInt)
    (hz : |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1) :
    Fits (2*q+8) z ∧ Fits (2*q+8) (unscaleBoundaryWord q z) := by
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have hone : (1 : ℝ) ≤ 2^p := one_le_pow₀ (by norm_num)
  have hC : 8*(p : ℝ)+1 ≤ (2 : ℝ)^(p+4) := by
    rw [pow_add]
    norm_num
    linarith
  have hgrid (a : ℤ) : gv q (a*(2 : ℤ)^(q/2+1)) = gv q a*(2 : ℝ)^(q/2+1) := by
    simp [gv]; ring
  have hbound (a : ℤ) (ha : |gv q a| ≤ 8*p+1) :
      |gv q (a*(2 : ℤ)^(q/2+1))| ≤ (2 : ℝ)^(p+4)*(2 : ℝ)^(q/2+1) := by
    rw [hgrid,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < 2^(q/2+1))]
    exact mul_le_mul_of_nonneg_right (ha.trans hC) (by positivity)
  have hwidth : ((2 : ℝ)^(p+4)*(2 : ℝ)^(q/2+1))*2^q < (2 : ℝ)^(2*q+8-1) := by
    rw [←pow_add,←pow_add]
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  have hwidth' : (2 : ℝ)^(p+4)*2^q < (2 : ℝ)^(2*q+8-1) := by
    rw [←pow_add]
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  refine ⟨fitsC_of_gv (hz.1.trans hC) (hz.2.trans hC) hwidth',?_⟩
  apply fitsC_of_gv (C := (2 : ℝ)^(p+4)*(2 : ℝ)^(q/2+1))
  · simpa [unscaleBoundaryWord,mul_real_re] using hbound z.re hz.1
  · simpa [unscaleBoundaryWord,mul_real_im] using hbound z.im hz.2
  · exact hwidth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
