import IntegerMultBounds.Machine.CompactReservationRate

/-! Uniform aggregation of paid individual-axis costs at the actual reservation
cutoff. This does not assume execution of an axis kernel: that physical proof
must supply its per-axis volume estimate. Both the volume and selected dimension
may vary arbitrarily with the input. -/
namespace IntegerMultBounds.Machine.CompactFallbackBudget
noncomputable section
open Filter Parameters Sizes CompactReservationCutoff

/-- The literal sum of the axis costs actually selected by the cutoff. -/
def cost (c m n D : ℕ) (axisCost : ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (processed c m n D), axisCost j

theorem cost_le (c m n D C volume : ℕ) (axisCost : ℕ → ℕ)
    (h : ∀ j < processed c m n D, axisCost j ≤ C*volume) :
    cost c m n D axisCost ≤ processed c m n D*(C*volume) := by
  unfold cost
  calc
    (∑ j ∈ Finset.range (processed c m n D), axisCost j) ≤
        ∑ _j ∈ Finset.range (processed c m n D), C*volume := by
      exact Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = processed c m n D*(C*volume) := by simp

/-- Any fixed linear-volume axis bound contributes arbitrarily little of the
certified layer allowance, simultaneously for all dimensions and volumes. -/
theorem eventually_cost (c m C : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ D volume : ℕ, ∀ axisCost : ℕ → ℕ,
      (∀ j < processed c m n D, axisCost j ≤ C*volume) →
      (cost c m n D axisCost : ℝ) ≤ η*(volume : ℝ)*(d n : ℝ)^lam' := by
  have hscale : (0 : ℝ) < (C : ℝ)+1 := by positivity
  filter_upwards [CompactReservationRate.eventually_processed_certified c m hm
    (η/((C : ℝ)+1)) (div_pos hη hscale)] with n hn D volume axisCost hc
  have hbound : (cost c m n D axisCost : ℝ) ≤
      (processed c m n D : ℝ)*((C : ℝ)*(volume : ℝ)) := by
    exact_mod_cast cost_le c m n D C volume axisCost hc
  have hC : (C : ℝ)/((C : ℝ)+1) ≤ 1 := by
    apply (div_le_iff₀ hscale).mpr
    linarith
  calc
    (cost c m n D axisCost : ℝ) ≤
        (processed c m n D : ℝ)*((C : ℝ)*(volume : ℝ)) := hbound
    _ ≤ (η/((C : ℝ)+1)*(d n : ℝ)^lam')*((C : ℝ)*(volume : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (hn D) (by positivity)
    _ = ((C : ℝ)/((C : ℝ)+1))*(η*(volume : ℝ)*(d n : ℝ)^lam') := by ring
    _ ≤ 1*(η*(volume : ℝ)*(d n : ℝ)^lam') := by
      exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = η*(volume : ℝ)*(d n : ℝ)^lam' := one_mul _

end
end IntegerMultBounds.Machine.CompactFallbackBudget
