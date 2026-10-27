module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineErrorBudget

/-! Cancel normalization in the complete boundary solve's forward-error estimate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

/-- The inverse scale cancels from RHS and matrix perturbations exactly. -/
theorem boundary_unscaled_error_identity (p q N : ℕ) (hp : 0 < p) (ε δ X E : ℝ) :
    (2 : ℝ)^(q/2+1) * (2 * (E +
      ((2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1)) +
        ((N : ℝ)*ε)*(X/(2 : ℝ)^(q/2+1)))/(1/(8*(2*(p : ℝ)))))) =
      2*((2 : ℝ)^(q/2+1)*E) +
        32*(p : ℝ)*((2 : ℝ)^(q/2+1)*(2/(2 : ℝ)^q) + δ + (N : ℝ)*ε*X) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  field_simp
  ring

/-- After unscaling only the small normalization roundtrip error remains;
retained RHS and matrix errors carry no exponential amplification. -/
theorem boundary_unscaled_total_error_budget (p u l target rhsExp N : ℕ) (hp : 0 < p)
    (ε δ X : ℝ) :
    let bits := boundaryTableBits p target rhsExp N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    (2 : ℝ)^(q/2+1) * (2 * (62000*(2*(p : ℝ))^3*(N : ℝ)^2*
      ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      ((2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1)) +
        ((N : ℝ)*ε)*(X/(2 : ℝ)^(q/2+1)))/(1/(8*(2*(p : ℝ)))))) ≤
      2/(2 : ℝ)^target +
        32*(p : ℝ)*(1/(2 : ℝ)^bits + δ + (N : ℝ)*ε*X) := by
  dsimp only
  rw [boundary_unscaled_error_identity p _ N hp]
  have hr := boundary_line_unscaled_roundoff_budget p u l target rhsExp N hp
  have hn := boundary_normalization_roundtrip_budget p u l target rhsExp N
  exact add_le_add (by simpa only [div_eq_mul_inv,mul_one,one_mul] using mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hn le_rfl) le_rfl) (by positivity))

/-- Existing table guard bits absorb both matrix and retained-RHS perturbations
when the original boundary solution has its stable polynomial magnitude. -/
theorem boundary_perturbation_target (p target rhsExp N : ℕ) (hp : 0 < p)
    (εA δ X : ℝ) (hX : 0 ≤ X)
    (hε : εA ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp)
    (hδ : δ ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp)
    (hbound : X ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp) :
    32*(p : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp N + δ + εA*X) ≤
      1/(2 : ℝ)^(target+1) := by
  let m : ℝ := 8*p
  let h := Nat.size (8*p)
  let ρ : ℝ := 2^rhsExp
  let η : ℝ := 1/(2 : ℝ)^boundaryErrorBits p target rhsExp
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1 ≤ 8*p)
  have hρ : 1 ≤ ρ := one_le_pow₀ (by norm_num)
  have hmPow : m ≤ (2 : ℝ)^h := by
    dsimp [m,h]
    exact_mod_cast (Nat.lt_size_self (8*p)).le
  have ht : 1/(2 : ℝ)^boundaryTableBits p target rhsExp N ≤ η := by
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [boundaryTableBits]
    omega
  have hb : X ≤ 2*m*ρ := by dsimp [m,ρ]; nlinarith only [hbound]
  have hprod : εA*X ≤ η*(2*m*ρ) := by
    exact (mul_le_mul_of_nonneg_right hε hX).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  have hcoeff : 8*m+8*m^2*ρ ≤ (2 : ℝ)^(2*h+rhsExp+4) := by
    have hm2 : m^2 ≤ ((2 : ℝ)^h)^2 := pow_le_pow_left₀ (by linarith) hmPow 2
    have hsmall : m ≤ m^2*ρ := by nlinarith
    calc
      _ ≤ 16*m^2*ρ := by nlinarith
      _ ≤ 16*((2 : ℝ)^h)^2*ρ := by gcongr
      _ = _ := by dsimp [ρ]; rw [← pow_mul]; simp only [pow_add]; norm_num; ring
  have hkernel : 32*(p : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp N + δ + εA*X) ≤
      (8*m+8*m^2*ρ)*η := by
    have hsum := add_le_add (add_le_add ht hδ) hprod
    have hs := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 32*p)
    dsimp [m] at *
    nlinarith only [hs]
  apply hkernel.trans
  apply (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans
  dsimp [η]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  dsimp [boundaryErrorBits,h]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
