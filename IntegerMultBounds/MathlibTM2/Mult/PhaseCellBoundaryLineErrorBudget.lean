module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLinePrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget

/-! The allocated solve accuracy survives exact unscaling. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

theorem boundary_line_error_precision (p u l target rhsExp N : ℕ) (hp : 0 < p) :
    let q := executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2
    5*p+2*Nat.size N+40+target+(q/2+1) ≤ q := by
  simp only [initialSchurTarget,recoveryFirstTarget_canonical]
  unfold executionPrecision executionExponent inputExponent sourceExponent recoveryTarget recoveryGuardBits
    boundaryTableBits boundaryErrorBits
  omega

theorem boundary_line_roundoff_target (p q N r : ℕ) (hp : 0 < p)
    (hbits : 5*p+2*Nat.size N+40+r ≤ q) :
    62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2)) ≤ 1/(2 : ℝ)^r := by
  have h := boundary_line_roundoff_budget p (q-r) N hp (by omega)
  have hq : q = (q-r)+r := by omega
  rw [hq,pow_add]
  calc
    _ = (62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/(2 : ℝ)^(q-r))*(1+60*3/(1/(32*(p : ℝ)))^2))) / (2 : ℝ)^r := by ring
    _ ≤ 1/(2 : ℝ)^r := div_le_div_of_nonneg_right h (by positivity)

theorem boundary_line_unscaled_roundoff_budget (p u l target rhsExp N : ℕ) (hp : 0 < p) :
    let q := executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2
    (2 : ℝ)^(q/2+1) * (62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/(2 : ℝ)^q)*(1+60*3/(1/(32*(p : ℝ)))^2))) ≤ 1/(2 : ℝ)^target := by
  dsimp only
  let q := executionPrecision p l
    (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2
  have h := boundary_line_roundoff_target p q N (target+(q/2+1)) hp
    (by have := boundary_line_error_precision p u l target rhsExp N hp; omega)
  calc
    _ ≤ (2 : ℝ)^(q/2+1) * (1/(2 : ℝ)^(target+(q/2+1))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1/(2 : ℝ)^target := by simp only [pow_add,pow_one]; field_simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
