import IntegerMultBounds.NLogN.Resampling
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons

/-! The sup-norm bound on the Gaussian resampling map `S`, Lemma 4.5 of
Harvey and van der Hoeven. Proved: the periodised Gaussian `θ_a` is even and
bounded by `1 + √(π/a)` through comparison with the Gaussian integral, and
consequently every entry of `S u` has modulus at most `1 + 1/α` whenever the
entries of `u` have modulus at most one. The companion map `T`, the square
subsystem, and its inverse are not treated here. -/

namespace IntegerMultBounds.NLogN

open Real MeasureTheory Set

variable {a : ℝ}

theorem gauss_neg (a x : ℝ) : gauss a (-x) = gauss a x := by
  simp [gauss]

theorem theta_neg (a x : ℝ) : theta a (-x) = theta a x := by
  unfold theta
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => gauss a (x + m))]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  rw [← gauss_neg]
  ring_nf

theorem continuous_gauss (a : ℝ) : Continuous (gauss a) := by
  unfold gauss
  fun_prop

theorem integrable_gauss (ha : 0 < a) : Integrable (gauss a) := by
  unfold gauss
  exact integrable_exp_neg_mul_sq ha

theorem integral_gauss (a : ℝ) : ∫ x, gauss a x = √(π / a) := by
  unfold gauss
  exact integral_gaussian a

/-- The positive tail `∑_{n ≥ 1} G(η + n)` is dominated by `∫_η^∞ G` when
`-1/2 ≤ η ≤ 0`. -/
theorem tsum_gauss_pos_tail_le (ha : 0 < a) {η : ℝ} (hη0 : -1 / 2 ≤ η) :
    ∑' n : ℕ, gauss a (η + ((n : ℝ) + 1)) ≤ ∫ y in Ioi η, gauss a y := by
  refine Real.tsum_le_of_sum_range_le (fun n => (gauss_pos _ _).le) (fun N => ?_)
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact setIntegral_nonneg measurableSet_Ioi (fun y _ => (gauss_pos _ _).le)
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add]
  have hcont := continuous_gauss a
  -- the first term is bounded by the integral over `[η, η + 1]`
  have h1 : gauss a (η + 1) ≤ ∫ y in η..η + 1, gauss a y := by
    have : ∫ y in η..η + 1, gauss a (η + 1) = gauss a (η + 1) := by
      rw [intervalIntegral.integral_const]; simp
    rw [← this]
    refine intervalIntegral.integral_mono_on (by linarith) (by simp)
      (hcont.intervalIntegrable _ _) (fun y hy => ?_)
    apply gauss_antitone_abs ha.le
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ η + 1)]
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  -- the remaining terms are bounded by the integral over `[η + 1, η + 1 + M]`
  have h2 : ∑ i ∈ Finset.range M, gauss a (η + (((i + 1 : ℕ) : ℝ) + 1)) ≤
      ∫ y in (η + 1)..(η + 1 + M), gauss a y := by
    have hanti : AntitoneOn (gauss a) (Icc (η + 1) (η + 1 + M)) := by
      intro y₁ hy₁ y₂ hy₂ hle
      apply gauss_antitone_abs ha.le
      rw [abs_of_nonneg (by linarith [hy₁.1]), abs_of_nonneg (by linarith [hy₂.1])]
      exact hle
    have := hanti.sum_le_integral
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  have hadd : (∫ y in η..η + 1, gauss a y) + ∫ y in (η + 1)..(η + 1 + M), gauss a y =
      ∫ y in η..(η + 1 + M), gauss a y :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have h3 : ∫ y in η..(η + 1 + M), gauss a y ≤ ∫ y in Ioi η, gauss a y := by
    rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])]
    refine setIntegral_mono_set (integrable_gauss ha).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos _ _).le)
      (Filter.Eventually.of_forall fun y hy => ?_)
    exact hy.1
  linarith

/-- The negative tail `∑_{n ≥ 1} G(η - n)` is dominated by `∫_{-∞}^η G` when
`η ≤ 0`. -/
theorem tsum_gauss_neg_tail_le (ha : 0 < a) {η : ℝ} (hη1 : η ≤ 0) :
    ∑' n : ℕ, gauss a (η + (-((n : ℝ) + 1))) ≤ ∫ y in Iic η, gauss a y := by
  refine Real.tsum_le_of_sum_range_le (fun n => (gauss_pos _ _).le) (fun N => ?_)
  have hcont := continuous_gauss a
  have hanti : AntitoneOn (fun y => gauss a (η - y)) (Icc (0 : ℝ) (0 + N)) := by
    intro y₁ hy₁ y₂ hy₂ hle
    apply gauss_antitone_abs ha.le
    rw [abs_of_nonpos (by linarith [hy₁.1]), abs_of_nonpos (by linarith [hy₂.1])]
    linarith
  have h1 := hanti.sum_le_integral
  have h2 : ∑ i ∈ Finset.range N, gauss a (η + (-((i : ℝ) + 1))) =
      ∑ i ∈ Finset.range N, gauss a (η - (0 + ((i + 1 : ℕ) : ℝ))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  rw [h2]
  refine le_trans h1 ?_
  rw [intervalIntegral.integral_comp_sub_left (fun y => gauss a y) η]
  rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
  refine setIntegral_mono_set (integrable_gauss ha).integrableOn
    (Filter.Eventually.of_forall fun y => (gauss_pos _ _).le)
    (Filter.Eventually.of_forall fun y hy => ?_)
  simp only [sub_zero] at hy
  exact hy.2

/-- The paper's bound `∑_j G(η + j) ≤ 1 + ∫ G` for `-1/2 ≤ η ≤ 0`. -/
theorem theta_le_one_add_integral (ha : 0 < a) {η : ℝ} (hη0 : -1 / 2 ≤ η) (hη1 : η ≤ 0) :
    theta a η ≤ 1 + √(π / a) := by
  have hpos : Summable (fun n : ℕ => gauss a (η + ((n : ℤ) : ℝ))) := by
    simpa only [Int.cast_natCast] using summable_gauss_nat ha η
  have hneg : Summable (fun n : ℕ => gauss a (η + ((-((n : ℤ) + 1) : ℤ) : ℝ))) := by
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    exact summable_gauss_of_le ha η (fun n => η + -((n : ℝ) + 1))
      (fun n => by nlinarith [sq_nonneg (2 * η - n - 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => gauss a (η + m)) hpos hneg
  unfold theta
  rw [hsplit]
  have hpos' : Summable (fun n : ℕ => (fun n : ℕ => gauss a (η + ((n : ℤ) : ℝ))) (n + 1)) := by
    refine (summable_gauss_nat ha (η + 1)).congr (fun n => ?_)
    push_cast
    ring_nf
  rw [tsum_eq_zero_add' (f := fun n : ℕ => gauss a (η + ((n : ℤ) : ℝ))) hpos']
  simp only [Nat.cast_zero, Int.cast_zero, add_zero, Int.cast_natCast, Int.cast_neg,
    Int.cast_add, Int.cast_one]
  have hP : ∑' n : ℕ, gauss a (η + (((n + 1 : ℕ) : ℝ))) ≤ ∫ y in Ioi η, gauss a y := by
    refine le_trans (le_of_eq (tsum_congr fun n => ?_)) (tsum_gauss_pos_tail_le ha hη0)
    push_cast
    rfl
  have hN := tsum_gauss_neg_tail_le ha hη1
  have h0 : gauss a η ≤ 1 := gauss_le_one ha.le η
  have hfull : (∫ y in Iic η, gauss a y) + ∫ y in Ioi η, gauss a y = √(π / a) := by
    rw [← integral_gauss a, ← integral_add_compl (μ := volume) measurableSet_Iic
      (integrable_gauss ha), compl_Iic]
  linarith

/-- The periodised Gaussian is bounded by `1 + √(π/a)` everywhere. -/
theorem theta_le_one_add_sqrt (ha : 0 < a) (x : ℝ) : theta a x ≤ 1 + √(π / a) := by
  -- reduce to a representative in `[-1/2, 1/2]`, then to `[-1/2, 0]` by evenness
  have hx : theta a x = theta a (x - round x) := by
    rw [sub_eq_add_neg, ← Int.cast_neg]
    exact (theta_add_int a x (-round x)).symm
  rw [hx]
  have hb := abs_sub_round x
  rw [abs_le] at hb
  rcases le_or_gt (x - round x) 0 with h | h
  · exact theta_le_one_add_integral ha (by linarith) h
  · rw [← theta_neg]
    exact theta_le_one_add_integral ha (by linarith) (by linarith)

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

omit [NeZero t] in
/-- The resampling weight is a translate of the periodised Gaussian's summand. -/
theorem resamp_weight_eq (hα : 0 < α) (k : ZMod t) (j : ℤ) :
    Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) =
      gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  unfold gauss
  congr 1
  field_simp
  ring

/-- Every entry of `S u` is bounded by `α⁻¹ θ(…)` when `‖u‖ ≤ 1`. -/
theorem norm_resampS_le_theta (hα : 0 < α) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (k : ZMod t) :
    ‖resampS s t α u k‖ ≤ (1 / α) * theta (π * α⁻¹ ^ 2) (-(s * k.val / t)) := by
  have hc : 0 < π * α⁻¹ ^ 2 := by positivity
  unfold resampS
  rw [norm_mul]
  have h1 : ‖(1 / α : ℂ)‖ = 1 / α := by
    rw [show (1 / α : ℂ) = ((1 / α : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : Summable (fun j : ℤ => gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j)) :=
    summable_gauss_int hc _
  have hterm : ∀ j : ℤ,
      ‖(Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j‖ ≤
        gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      resamp_weight_eq hα k j]
    calc gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) * ‖u j‖
        ≤ gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) * 1 :=
          mul_le_mul_of_nonneg_left (hu j) (gauss_pos _ _).le
      _ = _ := mul_one _
  have hnorm : Summable (fun j : ℤ =>
      ‖(Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j‖) :=
    hsum.of_nonneg_of_le (fun j => norm_nonneg _) hterm
  calc ‖∑' j : ℤ, (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j‖
      ≤ ∑' j : ℤ, ‖(Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℤ, gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) :=
        hnorm.tsum_le_tsum hterm hsum
    _ = theta (π * α⁻¹ ^ 2) (-(s * k.val / t)) := rfl

/-- Lemma 4.5: `‖S u‖ ≤ 1 + α⁻¹` in the sup norm. -/
theorem norm_resampS_le (hα : 0 < α) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1) (k : ZMod t) :
    ‖resampS s t α u k‖ ≤ 1 + 1 / α := by
  have hc : 0 < π * α⁻¹ ^ 2 := by positivity
  refine le_trans (norm_resampS_le_theta hα u hu k) ?_
  have hθ := theta_le_one_add_sqrt hc (-(s * k.val / t))
  have hsqrt : √(π / (π * α⁻¹ ^ 2)) = α := by
    rw [show π / (π * α⁻¹ ^ 2) = α ^ 2 by field_simp]
    exact Real.sqrt_sq hα.le
  rw [hsqrt] at hθ
  calc (1 / α) * theta (π * α⁻¹ ^ 2) (-(s * k.val / t))
      ≤ (1 / α) * (1 + α) := mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = 1 + 1 / α := by rw [mul_add, mul_one, one_div_mul_cancel hα.ne', add_comm]

end IntegerMultBounds.NLogN
