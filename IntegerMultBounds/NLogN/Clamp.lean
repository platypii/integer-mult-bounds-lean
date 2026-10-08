import IntegerMultBounds.NLogN.Approx

/-! Radial clamping to the closed unit disk, the paper's convention that every
numerical map returns values of modulus at most one. Proved: the clamp lands in
the disk, fixes the disk, does not increase norms, and is nonexpansive against
any point of the disk, componentwise and on vectors in the sup norm; hence an
approximation of a contraction may be clamped without increasing its scaled
error, which supplies the unit-ball side conditions of the composition lemmas;
the radius-`R` version; and rounding after clamping stays in the disk. No cost
is attached to the clamp. -/

open Complex

namespace IntegerMultBounds.NLogN

/-- Radial projection of a complex number onto the closed unit disk. -/
noncomputable def clampC (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then z else z / (‖z‖ : ℂ)

theorem clampC_of_le {z : ℂ} (h : ‖z‖ ≤ 1) : clampC z = z := by
  simp [clampC, h]

theorem norm_clampC_le_one (z : ℂ) : ‖clampC z‖ ≤ 1 := by
  unfold clampC
  split_ifs with h
  · exact h
  · push Not at h
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (by linarith)]

theorem norm_clampC_le (z : ℂ) : ‖clampC z‖ ≤ ‖z‖ := by
  unfold clampC
  split_ifs with h
  · exact le_rfl
  · push Not at h
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (by linarith)]
    exact h.le

/-- Clamping is nonexpansive against every point of the closed unit disk. -/
theorem norm_clampC_sub_le (z w : ℂ) (hw : ‖w‖ ≤ 1) : ‖clampC z - w‖ ≤ ‖z - w‖ := by
  unfold clampC
  split_ifs with h
  · exact le_rfl
  · push Not at h
    set ρ := ‖z‖ with hρ
    have hρpos : 0 < ρ := by linarith
    have hre : (z / (ρ : ℂ)).re = z.re / ρ := Complex.div_ofReal_re z ρ
    have him : (z / (ρ : ℂ)).im = z.im / ρ := Complex.div_ofReal_im z ρ
    have hz2 : z.re * z.re + z.im * z.im = ρ * ρ := by
      have := Complex.sq_norm z
      rw [Complex.normSq_apply] at this
      rw [← hρ] at this
      nlinarith [this]
    have hw2 : w.re * w.re + w.im * w.im ≤ 1 := by
      have := Complex.sq_norm w
      rw [Complex.normSq_apply] at this
      nlinarith [this, norm_nonneg w]
    set a := z.re / ρ with ha
    set b := z.im / ρ with hb
    have hza : z.re = ρ * a := by rw [ha]; field_simp
    have hzb : z.im = ρ * b := by rw [hb]; field_simp
    have hab : a * a + b * b = 1 := by
      have h1 : (a * a + b * b) * (ρ * ρ) = 1 * (ρ * ρ) := by
        rw [hza, hzb] at hz2; linear_combination hz2
      exact mul_right_cancel₀ (by positivity) h1
    set c := a * w.re + b * w.im with hc
    have hc2 : c * c ≤ 1 := by
      have : c * c + (a * w.im - b * w.re) * (a * w.im - b * w.re)
          = (a * a + b * b) * (w.re * w.re + w.im * w.im) := by rw [hc]; ring
      nlinarith [this, hab, hw2, mul_self_nonneg (a * w.im - b * w.re)]
    have hc1 : c ≤ 1 := by nlinarith [hc2]
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.sub_re, Complex.sub_im, hre, him]
    have key : (z.re - w.re) * (z.re - w.re) + (z.im - w.im) * (z.im - w.im)
        - ((a - w.re) * (a - w.re) + (b - w.im) * (b - w.im))
        = (ρ - 1) * (ρ + 1 - 2 * c) := by
      rw [hza, hzb, hc]; linear_combination (ρ ^ 2 - 1) * hab
    have hprod : 0 ≤ (ρ - 1) * (ρ + 1 - 2 * c) :=
      mul_nonneg (by linarith) (by linarith)
    linarith [key, hprod]

section Vec

variable {ι : Type*} [Fintype ι]

/-- Componentwise clamp of a vector into the unit ball of the sup norm. -/
noncomputable def clampV (v : ι → ℂ) : ι → ℂ := fun i => clampC (v i)

theorem norm_clampV_le_one (v : ι → ℂ) : ‖clampV v‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact norm_clampC_le_one (v i)

theorem norm_clampV_le (v : ι → ℂ) : ‖clampV v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  exact (norm_clampC_le (v i)).trans (norm_le_pi_norm v i)

theorem clampV_of_le {v : ι → ℂ} (h : ‖v‖ ≤ 1) : clampV v = v := by
  funext i
  exact clampC_of_le ((norm_le_pi_norm v i).trans h)

theorem norm_clampV_sub_le (v w : ι → ℂ) (hw : ‖w‖ ≤ 1) : ‖clampV v - w‖ ≤ ‖v - w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  calc ‖(clampV v - w) i‖ = ‖clampC (v i) - w i‖ := rfl
    _ ≤ ‖v i - w i‖ := norm_clampC_sub_le (v i) (w i) ((norm_le_pi_norm w i).trans hw)
    _ = ‖(v - w) i‖ := rfl
    _ ≤ ‖v - w‖ := norm_le_pi_norm (v - w) i

/-- Clamp into the ball of radius `R`. -/
noncomputable def clampVR (R : ℝ) (v : ι → ℂ) : ι → ℂ := (R : ℂ) • clampV ((R⁻¹ : ℂ) • v)

theorem norm_clampVR_le (R : ℝ) (hR : 0 < R) (v : ι → ℂ) : ‖clampVR R v‖ ≤ R := by
  unfold clampVR
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  calc R * ‖clampV ((R⁻¹ : ℂ) • v)‖ ≤ R * 1 :=
        mul_le_mul_of_nonneg_left (norm_clampV_le_one _) hR.le
    _ = R := mul_one R

theorem norm_clampVR_sub_le (R : ℝ) (hR : 0 < R) (v w : ι → ℂ) (hw : ‖w‖ ≤ R) :
    ‖clampVR R v - w‖ ≤ ‖v - w‖ := by
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hw' : ‖(R⁻¹ : ℂ) • w‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    rw [inv_mul_le_iff₀ hR, mul_one]
    exact hw
  have h1 : clampVR R v - w = (R : ℂ) • (clampV ((R⁻¹ : ℂ) • v) - (R⁻¹ : ℂ) • w) := by
    unfold clampVR
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hRne, one_smul]
  have h2 : v - w = (R : ℂ) • ((R⁻¹ : ℂ) • v - (R⁻¹ : ℂ) • w) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hRne, one_smul, smul_smul,
      mul_inv_cancel₀ hRne, one_smul]
  rw [h1, h2, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_clampV_sub_le _ _ hw') (norm_nonneg _)

end Vec

section Transfer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ι : Type*} [Fintype ι]

/-- Clamping an approximation of a contraction keeps its scaled error. -/
theorem approxMap_clamp {p : ℕ} {A' : V → (ι → ℂ)} {A : V →L[ℂ] (ι → ℂ)} {ε : ℝ}
    (hA : ‖A‖ ≤ 1) (h : ApproxMap p A' A ε) : ApproxMap p (clampV ∘ A') A ε := by
  intro v hv
  have hAv : ‖A v‖ ≤ 1 := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * 1 := mul_le_mul hA hv (norm_nonneg v) zero_le_one
      _ = 1 := one_mul 1
  calc (2 : ℝ) ^ p * ‖(clampV ∘ A') v - A v‖
      ≤ 2 ^ p * ‖A' v - A v‖ :=
        mul_le_mul_of_nonneg_left (norm_clampV_sub_le (A' v) (A v) hAv) (by positivity)
    _ ≤ ε := h v hv

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem clamp_ball (A' : V → (ι → ℂ)) (u : V) : ‖(clampV ∘ A') u‖ ≤ 1 :=
  norm_clampV_le_one (A' u)

theorem norm_rhoC_clampC_le_one (p : ℕ) (z : ℂ) : ‖rhoC p (clampC z)‖ ≤ 1 :=
  (norm_rhoC_le p (clampC z)).trans (norm_clampC_le_one z)

theorem norm_rd_clampV_le_one (p : ℕ) (v : ι → ℂ) :
    ‖fun i => rhoC p (clampV v i)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact norm_rhoC_clampC_le_one p (v i)

end Transfer

end IntegerMultBounds.NLogN
