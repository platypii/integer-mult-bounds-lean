module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitialErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryErrorBudget

/-! The retained execution precision pays the computed boundary factor's numerical and width bounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

theorem factor_execution_bits (p u l target rhsExp N : ℕ) :
    4*p+2*Nat.size N+36 ≤
      executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2 := by
  simp only [initialSchurTarget,recoveryFirstTarget_canonical]
  unfold executionPrecision executionExponent inputExponent sourceExponent recoveryTarget recoveryGuardBits
    boundaryTableBits boundaryErrorBits
  omega

private theorem factor_power_bound (p q c : ℕ) (hbits : p+c ≤ q) :
    (2 : ℝ)^c*(p : ℝ) ≤ (2 : ℝ)^q := by
  have hp : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  calc
    _ ≤ (2 : ℝ)^c*(2 : ℝ)^p := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 : ℝ)^(p+c) := by rw [←pow_add,Nat.add_comm]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hbits

theorem factor_roundoff_budget (p q : ℕ) (hp : 0 < p) (hbits : p+12 ≤ q) :
    5*(1/(2 : ℝ)^q) ≤ 2*((1/(32*(p : ℝ)))/4)/9 := by
  have hpow := factor_power_bound p q 12 hbits
  norm_num at hpow
  have he : 2*((1/(32*(p : ℝ)))/4)/9 = 1/(576*(p : ℝ)) := by ring
  rw [he,mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hpow]

theorem factor_record_width_budget (p q : ℕ) (hp : 0 < p) (hbits : p+2 ≤ q) :
    (6/(1/(32*(p : ℝ)))+1)*(2 : ℝ)^q < (2 : ℝ)^(2*q+8-1) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpow := factor_power_bound p q 2 hbits
  norm_num at hpow
  have hc : 6/(1/(32*(p : ℝ)))+1 = 192*p+1 := by field_simp; ring
  rw [hc]
  have h : 192*(p : ℝ)+1 < 128*(2 : ℝ)^q := by nlinarith only [hpow,hpR]
  have he : (2 : ℝ)^(2*q+8-1) = 128*(2 : ℝ)^q*(2 : ℝ)^q := by
    rw [show 2*q+8-1 = q+q+7 by omega]
    simp only [pow_add]
    norm_num
    ring
  rw [he]
  exact mul_lt_mul_of_pos_right h (by positivity)

theorem factor_stage_roundoff_budget (p q N : ℕ) (hp : 0 < p)
    (hbits : 4*p+2*Nat.size N+36 ≤ q) :
    2^16*(2*(p : ℝ))^2*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2)) ≤ 1 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have hNPow : (N : ℝ) ≤ (2 : ℝ)^Nat.size N := by exact_mod_cast (Nat.lt_size_self N).le
  have hc : 1+60*3/(1/(32*(p : ℝ)))^2 ≤ 262144*(p : ℝ)^2 := by
    have he : 1+60*3/(1/(32*(p : ℝ)))^2 = 1+184320*(p : ℝ)^2 := by field_simp; ring
    rw [he]
    nlinarith only [hpR]
  have hnum : 2^16*(2*(p : ℝ))^2*(N : ℝ)^2*(1+60*3/(1/(32*(p : ℝ)))^2) ≤
      (2 : ℝ)^(4*p+2*Nat.size N+36) := by
    calc
      _ ≤ 2^16*(2*(p : ℝ))^2*(N : ℝ)^2*(262144*(p : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (2 : ℝ)^36*(p : ℝ)^4*(N : ℝ)^2 := by norm_num; ring
      _ ≤ (2 : ℝ)^36*((2 : ℝ)^p)^4*((2 : ℝ)^Nat.size N)^2 := by gcongr
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add]; congr 1; omega
  have he : 2^16*(2*(p : ℝ))^2*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2)) =
      (2^16*(2*(p : ℝ))^2*(N : ℝ)^2*(1+60*3/(1/(32*(p : ℝ)))^2))/(2 : ℝ)^q := by ring
  rw [he]
  apply (div_le_one (by positivity)).mpr
  exact hnum.trans (pow_le_pow_right₀ (by norm_num) hbits)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
