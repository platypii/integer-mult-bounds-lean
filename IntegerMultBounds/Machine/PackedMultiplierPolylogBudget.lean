import IntegerMultBounds.CostTable

/-! A polylogarithmic overhead on the packed-product subroutine is absorbed by
the existing certified margin. This permits a proved Schonhage--Strassen tape
multiplier, rather than requiring an exact n log n subroutine bound. Actual
subroutine execution and its bit-cost estimate remain separate obligations. -/
namespace IntegerMultBounds.Machine.PackedMultiplierPolylogBudget
noncomputable section
open Filter Parameters Sizes TimeBound CostTable

/-- The nonnegative logarithmic overhead evaluated at the actual packed size. -/
def overhead (k : ℝ) (n : ℕ) : ℝ :=
  (1+max 0 (Real.log (packedProducts n)))^k

private theorem packed_constant : 4*Real.log 2+1/(1-epsilon) ≤ 6 := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : (0:ℝ)<1-epsilon := by norm_num [epsilon]
  have hd : 1/(1-epsilon) ≤ 2 := by
    apply (div_le_iff₀ he).mpr
    norm_num [epsilon]
  linarith

private theorem eventually_packed_linear :
    ∀ᶠ n : ℕ in atTop, packedProducts n ≤ 6*precision n := by
  filter_upwards [packedProducts_le] with n hn
  have hp : 1 ≤ precision n := by linarith [six_le_precision n]
  have he : 1-epsilon ≤ 1 := by norm_num [epsilon]
  have hpow := Real.rpow_le_rpow_of_exponent_le hp he
  have hC : 0 ≤ 4*Real.log 2+1/(1-epsilon) := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hd : 0 < 1-epsilon := by norm_num [epsilon]
    positivity
  calc
    packedProducts n ≤ (4*Real.log 2+1/(1-epsilon))*precision n^(1-margin 6) := hn
    _ ≤ 6*precision n^(1-epsilon) := by
      rw [margin_six]
      exact mul_le_mul_of_nonneg_right packed_constant (by positivity)
    _ ≤ 6*precision n := by simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤6)

/-- At the actual packed size, log log is at most a fixed multiple of log p. -/
theorem eventually_log_overhead :
    ∀ᶠ n : ℕ in atTop, 1+max 0 (Real.log (packedProducts n)) ≤ 7*Real.log (precision n) := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_precision).eventually_ge_atTop 1
  filter_upwards [eventually_packed_linear,hlog] with n hn hl
  change 1 ≤ Real.log (precision n) at hl
  have hp := precision_pos n
  have hupper : Real.log (packedProducts n) ≤ 5+Real.log (precision n) := by
    by_cases hc : 0 < packedProducts n
    · have h := Real.log_le_log hc hn
      rw [Real.log_mul (by norm_num : (6:ℝ)≠0) hp.ne'] at h
      have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)
      linarith
    · have hnonneg : 0 ≤ packedProducts n := by
        unfold packedProducts r
        apply Real.log_nonneg
        have hr : (1:ℝ) ≤ 2^ℓ n := one_le_pow₀ (by norm_num)
        nlinarith [six_le_precision n]
      have hz : packedProducts n=0 := by linarith
      rw [hz,Real.log_zero]
      linarith
  have hm : max 0 (Real.log (packedProducts n)) ≤ 5+Real.log (precision n) :=
    max_le (by linarith) hupper
  linarith

theorem eventually_overhead (k : ℝ) (hk : 0≤k) :
    ∀ᶠ n : ℕ in atTop, overhead k n ≤ 7^k*Real.log (precision n)^k := by
  filter_upwards [eventually_log_overhead] with n hn
  unfold overhead
  calc
    _ ≤ (7*Real.log (precision n))^k := Real.rpow_le_rpow (by positivity) hn hk
    _ = 7^k*Real.log (precision n)^k := Real.mul_rpow (by norm_num) (Real.log_nonneg (by linarith [six_le_precision n]))

/-- The packed-product row with this overhead is still below the claimed final
multiplier time, for every fixed nonnegative overhead exponent. -/
theorem eventually_time (k : ℝ) (hk : 0≤k) (V : ℕ → ℝ) (cV : ℝ)
    (hV0 : ∀ n,0≤V n) (hV : ∀ n,V n≤cV*n) :
    ∀ᶠ n : ℕ in atTop, V n*packedProducts n*overhead k n ≤
      ((4*Real.log 2+1/(1-epsilon))*7^k)*cV*6^(1-kappa)*targetTime kappa n := by
  let row : Row := ⟨(4*Real.log 2+1/(1-epsilon))*7^k,k,1-epsilon⟩
  have hC : 0≤row.C := by
    dsimp [row]
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hd : 0<1-epsilon := by norm_num [epsilon]
    positivity
  have he : row.e<1-kappa := by dsimp [row]; norm_num [epsilon,kappa]
  filter_upwards [packedProducts_le,eventually_overhead k hk,row_eventually V cV hV0 hV row hC he]
    with n hp ho hr
  have hnorm : V n*packedProducts n*overhead k n ≤ row.cost (V n) (precision n) := by
    calc
      _ ≤ (V n*((4*Real.log 2+1/(1-epsilon))*precision n^(1-margin 6)))*
          (7^k*Real.log (precision n)^k) := by
        gcongr
        · unfold overhead; positivity
        · have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          have hd : 0 < 1-epsilon := by norm_num [epsilon]
          exact mul_nonneg (hV0 n) (mul_nonneg
            (add_nonneg (mul_nonneg (by norm_num) hl) (one_div_nonneg.mpr hd.le))
            (Real.rpow_nonneg (precision_pos n).le _))
        · exact hV0 n
      _ = row.cost (V n) (precision n) := by rw [margin_six]; unfold Row.cost row; ring
  exact hnorm.trans hr

end
end IntegerMultBounds.Machine.PackedMultiplierPolylogBudget
