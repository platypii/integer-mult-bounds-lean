module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellTotalDyadicBudget

/-! A key exponent comparable to one axis logarithm turns the Euclidean
routing charge into dimension times axis-width cost, plus its short remainder. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds

theorem dyadicRouteCharge_le_axis (a b d ell : ℕ)
    (ha : a ≤ d*ell) (hb : b ≤ ell) (hell : ell ≤ 2*b) :
    dyadicRouteCharge a b ≤ 2*d*((ell : ℝ)^Parameters.tau+1)+4*ell := by
  have htau : 0 ≤ Parameters.tau := by norm_num [Parameters.tau]
  by_cases hz : b = 0
  · simp [dyadicRouteCharge,hz]
    positivity
  · have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hquot : (a : ℝ)/b ≤ 2*d := by
      apply (div_le_iff₀ hbpos).mpr
      have haR : (a : ℝ) ≤ d*ell := by exact_mod_cast ha
      have hellR : (ell : ℝ) ≤ 2*b := by exact_mod_cast hell
      nlinarith only [haR,mul_le_mul_of_nonneg_left hellR (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg b) (by exact_mod_cast hb : (b : ℝ) ≤ ell) htau
    have hmul := mul_le_mul hquot (add_le_add_right hpow 1)
      (by positivity) (by positivity : (0 : ℝ) ≤ 2*d)
    have hbR : (b : ℝ) ≤ ell := by exact_mod_cast hb
    unfold dyadicRouteCharge
    rw [if_neg hz]
    linarith only [hmul,hbR]

end IntegerMultBounds.MathlibTM2.Cost
