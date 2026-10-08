import IntegerMultBounds.CostTable

/-! Line counting for the tensor interface (§7, Lemma 7.2). Applying a
one-dimensional map along axis `i` of a box with `T = ∏ tⱼ` entries visits
`T / tᵢ` lines of length `tᵢ`, so one-dimensional work `C tᵢ X` per line sums
to `d C T X` over the `d` axes; with the Gaussian line cost `X = p^(3/2+δ) α`
this is the volume `T p` times the cost-table row `d p^(1/2+δ) α`. When every
`tᵢ ≥ r/2`, at most `2 d T / r` lines are visited in all, and any fixed
polynomial `p^c` of setup per line totals `o(T p)` under the size relations
of §8, because `r = 2^ℓ ≥ 2^(p^(1-ε)/12)` outgrows every power of `p`. -/

namespace IntegerMultBounds.LineCost

open Filter Topology Parameters TimeBound Sizes CostTable Asymptotics

/-! ### Counting lines -/

section Counting

variable {d : ℕ}

/-- One-dimensional work `C tᵢ X` on each of the `T / tᵢ` lines of axis `i`, summed
over the axes, is `d C T X`. -/
theorem linewise_sum (t : Fin d → ℝ) (ht : ∀ i, 0 < t i) (C X : ℝ) :
    ∑ i, (∏ j, t j) / t i * (C * t i * X) = d * C * (∏ j, t j) * X := by
  have h : ∀ i, (∏ j, t j) / t i * (C * t i * X) = C * (∏ j, t j) * X := fun i => by
    have := (ht i).ne'
    field_simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- With every `tᵢ ≥ r / 2`, the visited lines number at most `2 d T / r`. -/
theorem lines_le (t : Fin d → ℝ) (r : ℝ) (hr : 0 < r) (ht : ∀ i, r / 2 ≤ t i) :
    ∑ i, (∏ j, t j) / t i ≤ 2 * d * (∏ j, t j) / r := by
  have hpos : ∀ i, 0 < t i := fun i => lt_of_lt_of_le (by positivity) (ht i)
  have hT : 0 ≤ ∏ j, t j := Finset.prod_nonneg fun j _ => (hpos j).le
  have h : ∀ i, (∏ j, t j) / t i ≤ 2 * (∏ j, t j) / r := fun i => by
    calc (∏ j, t j) / t i ≤ (∏ j, t j) / (r / 2) :=
          div_le_div_of_nonneg_left hT (by positivity) (ht i)
      _ = 2 * (∏ j, t j) / r := by field_simp
  calc ∑ i, (∏ j, t j) / t i ≤ ∑ _i : Fin d, 2 * (∏ j, t j) / r := Finset.sum_le_sum fun i _ => h i
    _ = 2 * d * (∏ j, t j) / r := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Counting

/-! ### The Gaussian line row -/

/-- Lines of the box `T` with Gaussian cost `C tᵢ p^(3/2+δ) α` each: the total is the
volume `T p` times the cost-table row `gaussianLines = d p^(1/2+δ) α`. -/
theorem gaussian_lines_eq (n : ℕ) (t : Fin (d n) → ℝ) (ht : ∀ i, 0 < t i)
    (hT : ∏ j, t j = T n) (C : ℝ) :
    ∑ i, (∏ j, t j) / t i * (C * t i * (precision n ^ (3 / 2 + delta) * alpha n)) =
      C * (T n * precision n) * gaussianLines n := by
  rw [linewise_sum t ht, hT]
  unfold gaussianLines
  have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
  have e : precision n ^ (3 / 2 + delta) = precision n * precision n ^ (1 / 2 + delta) := by
    rw [show (3 / 2 + delta : ℝ) = 1 + (1 / 2 + delta) by ring, Real.rpow_add hp,
      Real.rpow_one]
  rw [e]
  ring

/-! ### Polynomial setup per line is negligible -/

/-- `x^s · 2^(-x^(1-ε)/12) → 0`: a power of `p` against the growth of `r`. -/
theorem tendsto_rpow_div_two_rpow (s : ℝ) :
    Tendsto (fun x : ℝ => x ^ s / (2 : ℝ) ^ (x ^ (1 - epsilon) / 12)) atTop (𝓝 0) := by
  have hε : 0 < 1 - epsilon := by norm_num [epsilon]
  have hb : 0 < Real.log 2 / 12 := by positivity
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / (1 - epsilon)) _ hb).comp
    (tendsto_rpow_atTop hε)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (x ^ (1 - epsilon) / 12),
    ← Real.rpow_mul hx.le]
  have e : x ^ ((1 - epsilon) * (s / (1 - epsilon))) = x ^ s := by
    congr 1
    field_simp
  rw [e, div_eq_mul_inv (x ^ s), ← Real.exp_neg]
  congr 2
  ring

/-- Under the size relations, `d p^c / r → 0` for every exponent `c`. -/
theorem tendsto_setup_ratio (c : ℝ) :
    Tendsto (fun n : ℕ => (d n : ℝ) * precision n ^ c / r n) atTop (𝓝 0) := by
  have hg := (tendsto_rpow_div_two_rpow (epsilon + c)).comp tendsto_precision
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards with n
    have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
    have hr : 0 < r n := by unfold r; positivity
    positivity
  · filter_upwards [eventually_r_ge] with n hr
    have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
    have h2 : (0 : ℝ) < 2 ^ (precision n ^ (1 - epsilon) / 12) := by positivity
    simp only [Function.comp]
    rw [Real.rpow_add hp]
    refine div_le_div₀ (by positivity) ?_ h2 hr
    exact mul_le_mul_of_nonneg_right (d_le n) (by positivity)

/-- Lemma 7.2, setup paragraph: `C d T p^c / r = o(T p)` for every degree `c`. -/
theorem setup_isLittleO (C c : ℝ) :
    (fun n : ℕ => C * d n * T n * precision n ^ c / r n) =o[atTop]
      fun n : ℕ => T n * precision n := by
  refine isLittleO_of_tendsto (fun n h => ?_) ?_
  · exfalso
    have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
    have := mul_pos (T_pos n) hp
    linarith
  · have h := (tendsto_setup_ratio (c - 1)).const_mul C
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with n
    have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
    have hr : 0 < r n := by unfold r; positivity
    have hT := T_pos n
    rw [Real.rpow_sub_one hp.ne']
    field_simp

/-- The negligible setup in the form the time bound consumes: eventually the per-line
polynomial setup over all visited lines is below the volume `T p`. -/
theorem eventually_setup_le (C c : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * d n * T n * precision n ^ c / r n ≤ T n * precision n := by
  have h := (setup_isLittleO C c).bound one_pos
  filter_upwards [h] with n hn
  have hp : 0 < precision n := lt_of_lt_of_le (by norm_num) (six_le_precision n)
  have hT := T_pos n
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hT hp)] at hn
  exact le_trans (le_abs_self _) hn

end IntegerMultBounds.LineCost
