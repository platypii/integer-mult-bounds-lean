module

public import IntegerMultBounds.MathlibTM2.Cost.ChirpSetupCost

/-! # One uniform cost allowance for the executed forward caller -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- A single universal constant for the total and amortized forward comparisons. -/
noncomputable def chirpForwardCostConstant : ℝ :=
  max (Classical.choose chirp_selected_total_le) (Classical.choose chirp_selected_amortized_le)

theorem chirpForwardCostConstant_nonneg : 0 ≤ chirpForwardCostConstant :=
  (Classical.choose_spec chirp_selected_total_le).1.trans (le_max_left _ _)

/-- Explicit setup plus repeated work, valid even for empty groups and short lines. -/
noncomputable def chirpGroupAllowance (s t α p N : ℕ) : ℝ :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let q := chirpForwardPrecision p (chirpForwardGrowth p) l
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  6000000 * ((t + m + 1 : ℕ) : ℝ) * ((W + 1 : ℕ) : ℝ) ^ 3 +
    chirpForwardCostConstant * (N : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)

/-- No primitive-cost or startup-cost assumption remains in the caller's allowance. -/
theorem chirp_selected_allowance_le (s t α p N : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤ chirpGroupAllowance s t α p N := by
  have hp : 1 ≤ p := hα.trans ((Nat.le_mul_self α).trans (by simpa only [pow_two] using hαp))
  have h := (Classical.choose_spec chirp_selected_total_le).2 p α s t N hp hα hαp hst
  have hC : Classical.choose chirp_selected_total_le ≤ chirpForwardCostConstant := le_max_left _ _
  have hwork := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N))
      (Nat.cast_nonneg (p ^ 2 + t))) (show 0 ≤ (p : ℝ) ^ (129 / 128 : ℝ) by positivity)
  exact h.trans (add_le_add le_rfl hwork)

/-- The complete scalar budget is amortized by explicit dimensions and the number of lines. -/
theorem chirp_selected_amortized_budget (s t α p N : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) (ht : p ^ 2 ≤ t)
    (hN : (chirpForwardTableWord
      (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α))
      (chirpForwardCallerBase s t p) + 1) ^ 3 ≤ N) :
    (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
      chirpForwardCostConstant * (N : ℝ) * (t : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  have hp : 1 ≤ p := hα.trans ((Nat.le_mul_self α).trans (by simpa only [pow_two] using hαp))
  have h := (Classical.choose_spec chirp_selected_amortized_le).2 p α s t N hp hα hαp hst ht hN
  have hC : Classical.choose chirp_selected_amortized_le ≤ chirpForwardCostConstant := le_max_right _ _
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N))
      (Nat.cast_nonneg t)) (by positivity))

end IntegerMultBounds.MathlibTM2.Cost
