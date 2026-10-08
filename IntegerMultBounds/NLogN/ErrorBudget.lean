import IntegerMultBounds.NLogN.FixedPoint

/-! Total error budget of the fixed-point convolution pipeline: forward
transforms of both inputs, pointwise product, inverse transform, division by
`2 ^ n`. Each stage is perturbed by explicit error oracles of size at most `ε`.
Proved: the perturbed pipeline is elementwise within an explicit expression in
`ε`, `A` (the input magnitude) and `n` of the exact one; that expression is at
most `5 * (2 ^ n) ^ 2 * A * ε` for `ε ≤ 1 ≤ A`; and with `ε = 1 / 2 ^ p` and
`2 ^ (2 * n + 4) * A ≤ 2 ^ p` it is below `1 / 2`, so rounding recovers exact
integer outputs. Whether the exact pipeline computes the convolution is the
business of the transform files; nothing here chooses `ω` or models the cost
of fixed-point arithmetic. -/

namespace IntegerMultBounds.NLogN

open Complex

/-- The exact three-stage pipeline, for any `ω`. -/
noncomputable def pipelineExact (n : ℕ) (ω : ℂ) (a b : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fun k => fft n ω⁻¹ (fun j => fft n ω a j * fft n ω b j) k / 2 ^ n

/-- The same pipeline with error oracles `e₁ e₂ e₃` inside the three
transforms and `r` added to the pointwise products. -/
noncomputable def pipelineErr (n : ℕ) (ω : ℂ) (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ)
    (r : Fin (2 ^ n) → ℂ) (a b : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fun k => fftErr n ω⁻¹ e₃ (fun j => fftErr n ω e₁ a j * fftErr n ω e₂ b j + r j) k / 2 ^ n

/-- The exact transform is additive. -/
theorem fft_sub : ∀ (n : ℕ) (ω : ℂ) (x y : Fin (2 ^ n) → ℂ) (k : Fin (2 ^ n)),
    fft n ω x k - fft n ω y k = fft n ω (fun j => x j - y j) k
  | 0, _, x, y, k => by simp [fft]
  | n + 1, ω, x, y, k => by
    have h1 := fft_sub n (ω ^ 2) (fun i => x (evenOddEquiv n (Sum.inl i)))
      (fun i => y (evenOddEquiv n (Sum.inl i))) (half n k)
    have h2 := fft_sub n (ω ^ 2) (fun i => x (evenOddEquiv n (Sum.inr i)))
      (fun i => y (evenOddEquiv n (Sum.inr i))) (half n k)
    simp only [fft]
    rw [← h1, ← h2]
    ring

/-- The explicit pipeline error expression. -/
noncomputable def pipelineBound (n : ℕ) (ε A : ℝ) : ℝ :=
  ((2 ^ n - 1) * ε + 2 ^ n * (2 * ((2 ^ n - 1) * ε) * (2 ^ n * A) +
    ((2 ^ n - 1) * ε) ^ 2 + ε)) / 2 ^ n

/-- Elementwise distance between the perturbed and exact pipelines. -/
theorem pipelineErr_sub (n : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) (ε A : ℝ)
    (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ) (r : Fin (2 ^ n) → ℂ)
    (a b : Fin (2 ^ n) → ℂ)
    (hε₁ : ∀ m k, ‖e₁ m k‖ ≤ ε) (hε₂ : ∀ m k, ‖e₂ m k‖ ≤ ε) (hε₃ : ∀ m k, ‖e₃ m k‖ ≤ ε)
    (hr : ∀ j, ‖r j‖ ≤ ε) (hA : ∀ j, ‖a j‖ ≤ A) (hB : ∀ j, ‖b j‖ ≤ A) (k : Fin (2 ^ n)) :
    ‖pipelineErr n ω e₁ e₂ e₃ r a b k - pipelineExact n ω a b k‖ ≤ pipelineBound n ε A := by
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hr ⟨0, by positivity⟩)
  have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hδ : 0 ≤ ((2 : ℝ) ^ n - 1) * ε := mul_nonneg (by linarith) hε
  have hωi : ‖ω⁻¹‖ = 1 := by rw [norm_inv, hω, inv_one]
  simp only [pipelineErr, pipelineExact, pipelineBound]
  set x : Fin (2 ^ n) → ℂ := fun j => fftErr n ω e₁ a j * fftErr n ω e₂ b j + r j with hx
  set y : Fin (2 ^ n) → ℂ := fun j => fft n ω a j * fft n ω b j with hy
  set η : ℝ := 2 * ((2 ^ n - 1) * ε) * (2 ^ n * A) + ((2 ^ n - 1) * ε) ^ 2 + ε with hη
  have hxy : ∀ j, ‖x j - y j‖ ≤ η := by
    intro j
    have ha' := fftErr_sub_fft n ω hω ε e₁ hε₁ a j
    have hb' := fftErr_sub_fft n ω hω ε e₂ hε₂ b j
    have hfa := fft_bound n ω hω A a hA j
    have hfb := fft_bound n ω hω A b hB j
    have hm := mul_err (fft n ω a j) (fftErr n ω e₁ a j) (fft n ω b j) (fftErr n ω e₂ b j)
    have hsplit : x j - y j =
        (fftErr n ω e₁ a j * fftErr n ω e₂ b j - fft n ω a j * fft n ω b j) + r j := by
      simp only [hx, hy]; ring
    rw [hsplit]
    calc _ ≤ ‖fftErr n ω e₁ a j * fftErr n ω e₂ b j - fft n ω a j * fft n ω b j‖ + ‖r j‖ :=
          norm_add_le _ _
      _ ≤ ((2 ^ n - 1) * ε) * (2 ^ n * A) + (2 ^ n * A) * ((2 ^ n - 1) * ε) +
            ((2 ^ n - 1) * ε) * ((2 ^ n - 1) * ε) + ε := by
          refine add_le_add (hm.trans ?_) (hr j)
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul ha' hfb (norm_nonneg _) hδ
          · exact mul_le_mul hfa hb' (norm_nonneg _) (mul_nonneg (by positivity) (le_trans (norm_nonneg _) (hA ⟨0, by positivity⟩)))
          · exact mul_le_mul ha' hb' (norm_nonneg _) hδ
      _ = η := by rw [hη]; ring
  have h3 := fftErr_sub_fft n ω⁻¹ hωi ε e₃ hε₃ x k
  have h4 : ‖fft n ω⁻¹ x k - fft n ω⁻¹ y k‖ ≤ 2 ^ n * η := by
    rw [fft_sub]
    exact fft_bound n ω⁻¹ hωi η (fun j => x j - y j) hxy k
  rw [← sub_div, norm_div, norm_pow, RCLike.norm_two]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _ ≤ ‖fftErr n ω⁻¹ e₃ x k - fft n ω⁻¹ x k‖ + ‖fft n ω⁻¹ x k - fft n ω⁻¹ y k‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 ^ n - 1) * ε + 2 ^ n * η := add_le_add h3 h4

/-- A simpler envelope for the error expression. -/
theorem pipelineBound_le (n : ℕ) {ε A : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A) :
    pipelineBound n ε A ≤ 5 * (2 ^ n) ^ 2 * A * ε := by
  unfold pipelineBound
  have hx : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  set x : ℝ := 2 ^ n with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hxm : 0 ≤ x - 1 := by linarith
  have hεε : ε * ε ≤ ε := mul_le_of_le_one_left hε hε1
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hx3 : x ^ 2 ≤ x ^ 3 := by nlinarith
  have hsq : (x - 1) ^ 2 ≤ x ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  -- the four summands, each at most `x ^ 3 * A * ε` up to its coefficient
  have t1 : (x - 1) * ε ≤ x ^ 3 * A * ε := by
    have : x - 1 ≤ x ^ 3 * A := by nlinarith
    exact mul_le_mul_of_nonneg_right this hε
  have t2 : x * (2 * ((x - 1) * ε) * (x * A)) ≤ 2 * (x ^ 3 * A * ε) := by
    have : x * ((x - 1) * (x * A)) ≤ x ^ 3 * A := by nlinarith
    nlinarith
  have t3 : x * ((x - 1) * ε) ^ 2 ≤ x ^ 3 * A * ε := by
    have h1 : x * ((x - 1) * ε) ^ 2 = x * (x - 1) ^ 2 * (ε * ε) := by ring
    have h2 : x * (x - 1) ^ 2 ≤ x ^ 3 := by nlinarith
    have h3 : x * (x - 1) ^ 2 * (ε * ε) ≤ x ^ 3 * ε := by
      calc x * (x - 1) ^ 2 * (ε * ε) ≤ x ^ 3 * (ε * ε) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ x ^ 3 * ε := mul_le_mul_of_nonneg_left hεε (by positivity)
    have h4 : x ^ 3 * ε ≤ x ^ 3 * A * ε := by
      have : x ^ 3 ≤ x ^ 3 * A := le_mul_of_one_le_right (by positivity) hA
      exact mul_le_mul_of_nonneg_right this hε
    linarith
  have t4 : x * ε ≤ x ^ 3 * A * ε := by
    have : x ≤ x ^ 3 * A := by nlinarith
    exact mul_le_mul_of_nonneg_right this hε
  nlinarith

/-- Precision `p` with `2 ^ p ≥ 2 ^ (2 n + 4) * A` keeps the total error below
`1 / 2`. -/
theorem precision_sufficient (n p : ℕ) {A : ℝ} (hA : 1 ≤ A)
    (hp : 2 ^ (2 * n + 4) * A ≤ (2 : ℝ) ^ p) :
    pipelineBound n (1 / 2 ^ p) A < 1 / 2 := by
  have hp0 : (0 : ℝ) < 2 ^ p := by positivity
  have hε : (0 : ℝ) ≤ 1 / 2 ^ p := by positivity
  have hε1 : (1 : ℝ) / 2 ^ p ≤ 1 := by
    rw [div_le_one hp0]; exact one_le_pow₀ (by norm_num)
  calc pipelineBound n (1 / 2 ^ p) A ≤ 5 * (2 ^ n) ^ 2 * A * (1 / 2 ^ p) :=
        pipelineBound_le n hε hε1 hA
    _ = 5 * ((2 ^ n) ^ 2 * A) / 2 ^ p := by ring
    _ ≤ 5 / 16 := by
        rw [div_le_div_iff₀ hp0 (by norm_num)]
        have : (2 : ℝ) ^ (2 * n + 4) = (2 ^ n) ^ 2 * 16 := by
          rw [pow_add, mul_comm 2 n, pow_mul]; norm_num
        rw [this] at hp
        linarith
    _ < 1 / 2 := by norm_num

/-- Rounding the perturbed pipeline recovers the exact integer outputs whenever
the error expression is below `1 / 2`. -/
theorem pipeline_exact_recovery (n : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) (ε A : ℝ)
    (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ) (r : Fin (2 ^ n) → ℂ)
    (a b : Fin (2 ^ n) → ℂ)
    (hε₁ : ∀ m k, ‖e₁ m k‖ ≤ ε) (hε₂ : ∀ m k, ‖e₂ m k‖ ≤ ε) (hε₃ : ∀ m k, ‖e₃ m k‖ ≤ ε)
    (hr : ∀ j, ‖r j‖ ≤ ε) (hA : ∀ j, ‖a j‖ ≤ A) (hB : ∀ j, ‖b j‖ ≤ A)
    (c : Fin (2 ^ n) → ℤ) (hc : pipelineExact n ω a b = fun k => (c k : ℂ))
    (hsmall : pipelineBound n ε A < 1 / 2) :
    (fun k => round (pipelineErr n ω e₁ e₂ e₃ r a b k).re) = c := by
  apply recover_of_close
  intro k
  have h := pipelineErr_sub n ω hω ε A e₁ e₂ e₃ r a b hε₁ hε₂ hε₃ hr hA hB k
  rw [hc] at h
  exact lt_of_le_of_lt h hsmall

/-- The same with the concrete precision `p`. -/
theorem pipeline_exact_recovery_pow (n p : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) (A : ℝ)
    (e₁ e₂ e₃ : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ) (r : Fin (2 ^ n) → ℂ)
    (a b : Fin (2 ^ n) → ℂ)
    (hε₁ : ∀ m k, ‖e₁ m k‖ ≤ 1 / 2 ^ p) (hε₂ : ∀ m k, ‖e₂ m k‖ ≤ 1 / 2 ^ p)
    (hε₃ : ∀ m k, ‖e₃ m k‖ ≤ 1 / 2 ^ p) (hr : ∀ j, ‖r j‖ ≤ 1 / 2 ^ p)
    (hA : ∀ j, ‖a j‖ ≤ A) (hB : ∀ j, ‖b j‖ ≤ A) (hA1 : 1 ≤ A)
    (hp : 2 ^ (2 * n + 4) * A ≤ (2 : ℝ) ^ p)
    (c : Fin (2 ^ n) → ℤ) (hc : pipelineExact n ω a b = fun k => (c k : ℂ)) :
    (fun k => round (pipelineErr n ω e₁ e₂ e₃ r a b k).re) = c :=
  pipeline_exact_recovery n ω hω (1 / 2 ^ p) A e₁ e₂ e₃ r a b hε₁ hε₂ hε₃ hr hA hB c hc
    (precision_sufficient n p hA1 hp)

end IntegerMultBounds.NLogN
