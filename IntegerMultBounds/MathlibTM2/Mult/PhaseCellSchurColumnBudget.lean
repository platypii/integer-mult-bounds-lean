module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryErrorBudget

/-! Allocate original-column accuracy separately from executed residual accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds

def schurColumnBits (p entryBits : ℕ) : ℕ := entryBits+Nat.size (1+16*p)+1

theorem schurColumn_input_budget (p entryBits : ℕ) :
    (1+16*(p : ℝ))*(1/(2 : ℝ)^schurColumnBits p entryBits) ≤ 1/(2 : ℝ)^(entryBits+1) := by
  have hm : (1+16*(p : ℝ)) ≤ (2 : ℝ)^Nat.size (1+16*p) := by
    exact_mod_cast (Nat.lt_size_self (1+16*p)).le
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (2 : ℝ)^Nat.size (1+16*p)*(2 : ℝ)^(entryBits+1) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by
      rw [one_mul,← pow_add]
      congr 1
      dsimp [schurColumnBits]
      omega

theorem schurColumn_pass_budget (p entryBits : ℕ) (hp : 0 < p) :
    (1/(2 : ℝ)^(recoveryTarget p entryBits+2))/(8*(p : ℝ)) ≤ 1/(2 : ℝ)^(entryBits+1) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  calc
    _ ≤ 1/(2 : ℝ)^(recoveryTarget p entryBits+2) := div_le_self (by positivity) (by linarith)
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      dsimp [recoveryTarget]
      omega

theorem schurColumn_total_budget (p entryBits : ℕ) (hp : 0 < p) {η : ℝ}
    (hη : η ≤ 1/(2 : ℝ)^schurColumnBits p entryBits) :
    (1/(2 : ℝ)^(recoveryTarget p entryBits+2))/(8*(p : ℝ))+(1+16*(p : ℝ))*η ≤
      1/(2 : ℝ)^entryBits := by
  have hc := (mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ 1+16*(p : ℝ))).trans
    (schurColumn_input_budget p entryBits)
  have hh := add_le_add (schurColumn_pass_budget p entryBits hp) hc
  simpa only [component_error_budget] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
