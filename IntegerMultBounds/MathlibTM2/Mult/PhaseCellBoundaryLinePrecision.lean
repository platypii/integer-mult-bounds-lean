module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPrecisionBudget

/-! The allocated precision also pays the triangular solve's perturbation bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

theorem boundary_line_execution_bits (p u l target rhsExp N : ℕ) :
    5*p+2*Nat.size N+40 ≤
      executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2 := by
  simp only [initialSchurTarget,recoveryFirstTarget_canonical]
  unfold executionPrecision executionExponent inputExponent sourceExponent recoveryTarget recoveryGuardBits
    boundaryTableBits boundaryErrorBits
  omega

theorem boundary_line_roundoff_budget (p q N : ℕ) (hp : 0 < p)
    (hbits : 5*p+2*Nat.size N+40 ≤ q) :
    62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2)) ≤ 1 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have hNPow : (N : ℝ) ≤ (2 : ℝ)^Nat.size N := by exact_mod_cast (Nat.lt_size_self N).le
  have hc : 1+60*3/(1/(32*(p : ℝ)))^2 ≤ 262144*(p : ℝ)^2 := by
    have he : 1+60*3/(1/(32*(p : ℝ)))^2 = 1+184320*(p : ℝ)^2 := by field_simp; ring
    rw [he]
    nlinarith only [hpR]
  have hnum : 62000*(2*(p : ℝ))^3*(N : ℝ)^2*(1+60*3/(1/(32*(p : ℝ)))^2) ≤
      (2 : ℝ)^(5*p+2*Nat.size N+40) := by
    calc
      _ ≤ 62000*(2*(p : ℝ))^3*(N : ℝ)^2*(262144*(p : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (62000*8*262144 : ℝ)*(p : ℝ)^5*(N : ℝ)^2 := by ring
      _ ≤ (2 : ℝ)^40*(p : ℝ)^5*(N : ℝ)^2 := by gcongr; norm_num
      _ ≤ (2 : ℝ)^40*((2 : ℝ)^p)^5*((2 : ℝ)^Nat.size N)^2 := by gcongr
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add]; congr 1; omega
  have he : 62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2)) =
      (62000*(2*(p : ℝ))^3*(N : ℝ)^2*(1+60*3/(1/(32*(p : ℝ)))^2))/(2 : ℝ)^q := by ring
  rw [he]
  apply (div_le_one (by positivity)).mpr
  exact hnum.trans (pow_le_pow_right₀ (by norm_num) hbits)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
