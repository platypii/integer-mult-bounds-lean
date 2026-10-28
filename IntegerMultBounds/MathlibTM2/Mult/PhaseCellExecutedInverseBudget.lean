module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedRealSolveSpec

/-! Derived precision absorbs input quantization; one extra target bit pays both errors. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem inverseFullInputPrecision_ge (p u l target s t : ℕ) [NeZero s] :
    target+8*p ≤ inverseFullInputPrecision p u l target s t := by
  unfold inverseFullInputPrecision executionPrecision
  rw [← inverseExecutionExponent_eq]
  unfold inverseExecutionExponent
  omega

theorem inverseFullInput_rounding_budget (p u l target s t : ℕ) [NeZero s] :
    8*(p : ℝ)/(2 : ℝ)^(inverseFullInputPrecision p u l target s t) ≤ 1/(2 : ℝ)^target := by
  have hp : 8*(p : ℝ) ≤ (2 : ℝ)^(8*p) := by exact_mod_cast (show 8*p < 2^(8*p) from Nat.lt_two_pow_self).le
  have hq := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (inverseFullInputPrecision_ge p u l target s t)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    8*(p : ℝ)*(2 : ℝ)^target ≤ (2 : ℝ)^(8*p)*(2 : ℝ)^target := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (2 : ℝ)^(target+8*p) := by rw [pow_add]; ring
    _ ≤ 1*(2 : ℝ)^(inverseFullInputPrecision p u l target s t) := by simpa only [one_mul] using hq

theorem executedRealInverse_dyadic_spec {Q A s : ℕ} [NeZero s] {U : Type}
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target t : ℕ} {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 303 Q A U) :
    SolveSpec (realMatrix s t p u) Finset.univ Finset.univ (1/2)
      (executedRealInverse recovery hR hQ p u l (target+1) t v) (1/(2 : ℝ)^target) := by
  apply (executedRealInverse_spec recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad v (target := target+1)).mono_error
  have he := inverseFullInput_rounding_budget p u l (target+1) s t
  have hp : 2/(2 : ℝ)^(target+1) = 1/(2 : ℝ)^target := by rw [pow_succ]; field_simp
  calc
    _ ≤ 1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1) := add_le_add_right he _
    _ = 1/(2 : ℝ)^target := by rw [← hp]; ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
