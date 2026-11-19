module

public import IntegerMultBounds.Parameters

/-! Arithmetic candidate for the first compact-runtime integration. These
inequalities are not a multiplication-time theorem. Actual caller and cost
assembly must replace the old full-width chunk estimate before using them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.CompactInterim
noncomputable section

/-- Preserve the actual dimension exponent. -/
def epsilon : ℝ := 31 / (2^6:ℝ)
/-- The layer exponent of the T16 node: above `τ` and above `log_m (F / NW) < 999/1000`
(`Cost.br_branching_999`). -/
def lam : ℝ := 1-12389971/(10^11:ℝ)
/-- Absorb the full-depth compact recurrence and all polylogarithmic factors. -/
def lam' : ℝ := 1-12389970/(10^11:ℝ)
/-- Dyadic allowance for the unchanged quasi-linear multiplier. -/
def delta : ℝ := (2^7:ℝ)⁻¹
/-- The public saving: the layer margin `ε (1-λ')` rounded down to `2^-46`, about `2^-14.02`. -/
def kappa : ℝ := 4223103985/(2^46:ℝ)

/-- The compact recurrence and reserved axes fit strictly below the target
layer exponent; this does not assert the old full-width recurrence condition. -/
theorem compact_slacks :
    0 < epsilon ∧ Parameters.tau < lam ∧ 999/1000 < lam ∧ lam < lam' ∧ lam' < 1 := by
  norm_num [epsilon,lam,lam',Parameters.tau]

/-- Exact candidate margins for layout with the half-dimension chunk, compact layers, direct
rounds with the legacy `2^-32` chunk, CRT, and the resampling stage with the logarithmic band
width `α ≤ 4 b^{ε/2^33}`. -/
def margin : Fin 5 → ℝ := ![
  epsilon*(1-Parameters.tau),
  epsilon*(1-lam'),
  epsilon*(1-(2^32:ℝ)⁻¹),
  (1-epsilon)*(1-Parameters.tau),
  1/2-delta-epsilon*(1+(2^33:ℝ)⁻¹)]

theorem margin_covers (i : Fin 5) : kappa ≤ margin i := by
  fin_cases i <;> norm_num [margin,kappa,epsilon,lam',delta,Parameters.tau]

end
end IntegerMultBounds.MathlibTM2.Cost.CompactInterim
