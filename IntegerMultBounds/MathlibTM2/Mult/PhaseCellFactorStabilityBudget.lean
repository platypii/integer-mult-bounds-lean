module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryErrorBudget
public import IntegerMultBounds.NLogN.SchurLUBackward

/-! The existing boundary-table precision allocation leaves a positive factorization margin. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.SchurDominance

theorem boundaryTable_factor_margin_budget (p target rhsExp N : ℕ) (hp : 0 < p) :
    (N : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp N) ≤ 1/(16*(p : ℝ)) := by
  have hpow : (8*(p : ℝ)) ≤ (2 : ℝ)^Nat.size (8*p) := by
    exact_mod_cast (Nat.lt_size_self (8*p)).le
  have hη : 1/(2 : ℝ)^boundaryErrorBits p target rhsExp ≤
      1/((2 : ℝ)^Nat.size (8*p)*2) := by
    rw [show (2 : ℝ)^Nat.size (8*p)*2 = 2^(Nat.size (8*p)+1) by rw [pow_succ]]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    unfold boundaryErrorBits
    omega
  apply (boundaryTable_error_budget p target rhsExp N).trans (hη.trans ?_)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [hpow]

theorem boundaryFactor_stageInv_allocated (M : Matrix ℕ ℕ ℝ) (p target rhsExp N : ℕ) (hp : 2 ≤ p)
    (hM : StageInv M (Finset.range N)
      (1/(8*(p : ℝ))-(N : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp N))
      (2+(N : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp N))) :
    StageInv M (Finset.range N) (1/(8*(2*(p : ℝ)))) (9/4) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hmargin := boundaryTable_factor_margin_budget p target rhsExp N (by omega)
  have hhalf : (1 : ℝ)/(8*p) = 2*(1/(16*p)) := by field_simp; ring
  have hμ : (1 : ℝ)/(8*(2*p)) = 1/(16*p) := by congr 1; ring
  have hquarter : (1 : ℝ)/(16*p) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith only [hpR]
  apply stageInv_mono M (Finset.range N) hM
  · rw [hμ,hhalf]
    linarith only [hmargin]
  · linarith only [hmargin,hquarter]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
