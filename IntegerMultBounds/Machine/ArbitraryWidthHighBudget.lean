import IntegerMultBounds.Machine.ArbitraryWidthHighGuard

/-! The actual high-digit count is bounded by every positive width power.
This pays for high-prefix exchanges and ordered joining/separation without
weakening the certified exponent of the recursive interchange. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighBudget
noncomputable section
open ArbitraryWidthHighPrepare

def slope (q : ℕ) : ℝ := Real.log worlds/(2*Real.log q)
def constant (q : ℕ) (τ : ℝ) : ℝ := slope q/Real.log base/τ+slope q+2

theorem slope_nonnegative (q : ℕ) (hq : 2 ≤ q) : 0 ≤ slope q := by
  have hW : (1 : ℝ) ≤ worlds := by exact_mod_cast le_trans (by decide : 1 ≤ base) worlds_ge_base
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  unfold slope
  exact div_nonneg (Real.log_nonneg hW) (by positivity)

theorem constant_positive (q : ℕ) (τ : ℝ) (hq : 2 ≤ q) (hτ : 0 < τ) : 0 < constant q τ := by
  have hs := slope_nonnegative q hq
  have hb : 0 < Real.log base := Real.log_pos (by norm_num [base])
  unfold constant
  positivity

/-- The count returned by the actual integer selector obeys the bound for
all positive widths, including those handled by the bounded fallback. -/
theorem count_bound (q e : ℕ) (τ : ℝ) (hq : 2 ≤ q) (he : 0 < e) (hτ : 0 < τ) :
    (highDepth q e : ℝ)+1 ≤ constant q τ*(e : ℝ)^τ := by
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hb : 0 < Real.log base := Real.log_pos (by norm_num [base])
  have hs := slope_nonnegative q hq
  have hl : 0 ≤ Real.log e := Real.log_nonneg he1
  have hk : (depth e : ℝ) < Real.log e/Real.log base+1 := by
    rw [ArbitraryWidthHighGuard.depth_eq_ceiling]
    exact Nat.ceil_lt_add_one (div_nonneg hl hb.le)
  have hr : (highDepth q e : ℝ) < (depth e : ℝ)*slope q+1 := by
    rw [selector_eq_manuscript q e hq,← worlds_eq_W]
    have heq : (depth e : ℝ)*Real.log worlds/(2*Real.log q) = (depth e : ℝ)*slope q := by
      unfold slope; ring
    rw [heq]
    exact Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) hs)
  have hm := mul_le_mul_of_nonneg_right hk.le hs
  have ha : (highDepth q e : ℝ)+1 ≤ slope q/Real.log base*Real.log e+slope q+2 := by
    have ht : (Real.log e/Real.log base+1)*slope q =
        slope q/Real.log base*Real.log e+slope q := by ring
    rw [ht] at hm
    linarith
  have hp : 1 ≤ (e : ℝ)^τ := Real.one_le_rpow he1 hτ.le
  have hlog := mul_le_mul_of_nonneg_left (Real.log_natCast_le_rpow_div e hτ)
    (div_nonneg hs hb.le)
  have hc := mul_le_mul_of_nonneg_left hp (show 0 ≤ slope q+2 by linarith)
  have ht : slope q/Real.log base*((e : ℝ)^τ/τ)+(slope q+2)*(e : ℝ)^τ =
      constant q τ*(e : ℝ)^τ := by unfold constant; ring
  rw [← ht]
  exact ha.trans (by linarith)

/-- Any fixed-coefficient linear-per-digit movement cost fits the unchanged
positive width exponent after multiplying by the actual parent volume. -/
theorem movement_bound (q e V K : ℕ) (τ : ℝ) (hq : 2 ≤ q) (he : 0 < e) (hτ : 0 < τ) :
    (K : ℝ)*((highDepth q e : ℝ)+1)*V ≤
      ((K : ℝ)*constant q τ)*(V : ℝ)*(e : ℝ)^τ := by
  have h := mul_le_mul_of_nonneg_left (count_bound q e τ hq he hτ)
    (show 0 ≤ (K : ℝ)*(V : ℝ) by positivity)
  nlinarith

end
end IntegerMultBounds.Machine.ArbitraryWidthHighBudget
