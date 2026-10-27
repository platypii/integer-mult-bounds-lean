module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalization

/-! Half the allocated working precision bounds the retained Schur RHS and leaves accuracy guards. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem boundary_normalization_precision (p u l target rhsExp N : ℕ) :
    let bits := boundaryTableBits p target rhsExp N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    2 ≤ q ∧ q%2 = 0 ∧
      couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ≤ q/2 ∧
      bits+4 ≤ q/2 := by
  simp only [initialSchurTarget,recoveryFirstTarget_canonical]
  unfold executionPrecision executionExponent inputExponent sourceExponent recoveryTarget recoveryGuardBits
    boundaryTableBits boundaryErrorBits couplingRowExponent stableInteriorExponent
  omega

/-- Undoing normalization still leaves the allocated matrix/solve target's guard bits. -/
theorem boundary_normalization_roundtrip_budget (p u l target rhsExp N : ℕ) :
    let bits := boundaryTableBits p target rhsExp N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    (2 : ℝ)^(q/2+1)*(2/(2 : ℝ)^q) ≤ 1/(2 : ℝ)^bits := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  obtain ⟨hq,heven,hmag,hbits⟩ := boundary_normalization_precision p u l target rhsExp N
  change (2 : ℝ)^(q/2+1)*(2/(2 : ℝ)^q) ≤ 1/(2 : ℝ)^bits
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnum : (2 : ℝ)^(q/2+1)*2*(2 : ℝ)^bits = (2 : ℝ)^(q/2+bits+2) := by
    rw [show q/2+bits+2 = (q/2+1)+1+bits by omega]
    simp only [pow_add,pow_one]
  rw [hnum,one_mul]
  apply pow_le_pow_right₀ (by norm_num)
  change q%2 = 0 at heven
  change bits+4 ≤ q/2 at hbits
  omega

/-- The actual initial residual's magnitude bound implies the normalization kernel's bound. -/
theorem boundary_residual_normalization_bound (p u l target rhsExp N : ℕ) (z : GaussianInt)
    (hz : |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2) z.re| ≤
        (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2) z.im| ≤
        (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) :
    let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp N) 2) 2
    |gv q z.re| ≤ (2 : ℝ)^(q/2) ∧ |gv q z.im| ≤ (2 : ℝ)^(q/2) := by
  have h := (boundary_normalization_precision p u l target rhsExp N).2.2.1
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
  exact ⟨hz.1.trans hpow,hz.2.trans hpow⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
