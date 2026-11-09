module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing

/-! Price the actual joint boundary batch using the existing prepared kernel
estimate. Counter setup occurs once; solve and stream costs repeat per RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem preparedResidualBatch_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q N W replicas : ℕ,
      1 ≤ p → 2*q+8 ≤ cw*p → 1 ≤ W →
      (preparedResidualBatchCost q (2*q+8) N W replicas : ℝ) ≤
        (N*(6*(2*q+8)+9)+16 : ℕ)+
          replicas*(C*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ)+
            (22*N*(2*q+8)+25 : ℕ)) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidual_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p q N W replicas hp hw hW
  have h := hfast p q N W hp hw hW
  unfold preparedResidualBatchCost
  push_cast
  have hr := mul_le_mul_of_nonneg_left
    (add_le_add h (le_refl ((22*N*(2*q+8)+25 : ℕ) : ℝ))) (Nat.cast_nonneg replicas)
  push_cast at hr
  simpa only [add_assoc] using add_le_add (le_refl ((N : ℝ)*(6*(2*q+8)+9)+16)) hr

/-- The cyclic caller's actual precision and width satisfy the prepared-kernel
identity, so its batch bill inherits the same bound without a width supplier. -/
theorem preparedResidualBatch_execution_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target rhsExp N W replicas : ℕ,
      1 ≤ p → executionWidth p l target rhsExp ≤ cw*p → 1 ≤ W →
      let q := executionPrecision p l target rhsExp
      let w := executionWidth p l target rhsExp
      (preparedResidualBatchCost q w N W replicas : ℝ) ≤
        (N*(6*w+9)+16 : ℕ)+
          replicas*(C*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ)+
            (22*N*w+25 : ℕ)) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidualBatch_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p l target rhsExp N W replicas hp hw hW
  have heq : executionWidth p l target rhsExp =
      2*executionPrecision p l target rhsExp+8 := by
    unfold executionWidth executionPrecision
    omega
  dsimp only
  rw [heq] at hw ⊢
  exact hfast p _ N W replicas hp hw hW

end IntegerMultBounds.MathlibTM2.Cost
