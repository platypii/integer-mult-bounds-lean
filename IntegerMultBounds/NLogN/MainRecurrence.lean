import IntegerMultBounds.NLogN.Recurrence

/-! Corollary 5.5 and the proof of Theorem 1.1 of Harvey–van der Hoeven, in
the abstract. Given the recursive cost inequality (5.14),
`M n ≤ (12 T / r) M (3 r p) + A n log n`, and the parameter facts
`T p ≤ 48 n`, `2 ≤ 3 r p < n`, and `log (3 r p) ≤ (1/d + 1/(2d²)) log n`,
the normalised cost satisfies `T(n) ≤ (1728/d)(1 + 1/(2d)) T(3rp) + A`; the
coefficient is at most `0.9998` once `d ≥ 1729`, and the contraction lemma
gives `M n = O(n log n)`. Every fact about the parameters `T`, `r`, `p` and
the recursive inequality itself is a hypothesis here; nothing about an actual
algorithm is established. -/

namespace IntegerMultBounds.NLogN

/-- Corollary 5.5: dividing (5.14) by `n log n`. Here `m = 3 r p`. -/
theorem normalised_step {M : ℕ → ℝ} {n m T r p : ℕ} {A d : ℝ}
    (hn2 : 2 ≤ n) (hm : (m : ℝ) = 3 * r * p) (hm2 : 2 ≤ m)
    (hTp : (T : ℝ) * p ≤ 48 * n)
    (hlog : Real.log m ≤ (1 / d + 1 / (2 * d ^ 2)) * Real.log n)
    (hrec : M n ≤ 12 * (T : ℝ) / r * M m + A * n * Real.log n)
    (hM : 0 ≤ M m) (hd : 1 ≤ d) (hr : 0 < r) :
    M n / (n * Real.log n) ≤
      (1728 / d) * (1 + 1 / (2 * d)) * (M m / (m * Real.log m)) + A := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm2
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hL : 0 < (n : ℝ) * Real.log n := mul_pos (by linarith) hlogn
  have hLm : 0 < (m : ℝ) * Real.log m := mul_pos (by linarith) hlogm
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : 0 < d := by linarith
  have hK : (1728 / d) * (1 + 1 / (2 * d)) = 1728 * (1 / d + 1 / (2 * d ^ 2)) := by
    field_simp
  rw [hK, div_le_iff₀ hL]
  have hcoef : 12 * (T : ℝ) / r * ((m : ℝ) * Real.log m) ≤
      1728 * (1 / d + 1 / (2 * d ^ 2)) * ((n : ℝ) * Real.log n) := by
    have h1 : 12 * (T : ℝ) / r * ((m : ℝ) * Real.log m) =
        36 * ((T : ℝ) * p) * Real.log m := by
      rw [hm]
      field_simp
      ring
    rw [h1]
    have hTp0 : 0 ≤ (T : ℝ) * p := by positivity
    have hc : 0 ≤ 1 / d + 1 / (2 * d ^ 2) := by positivity
    calc 36 * ((T : ℝ) * p) * Real.log m
        ≤ 36 * ((T : ℝ) * p) * ((1 / d + 1 / (2 * d ^ 2)) * Real.log n) := by
          gcongr
      _ ≤ 36 * (48 * n) * ((1 / d + 1 / (2 * d ^ 2)) * Real.log n) := by
          gcongr
      _ = _ := by ring
  have hmain : 12 * (T : ℝ) / r * M m ≤
      1728 * (1 / d + 1 / (2 * d ^ 2)) * (M m / (m * Real.log m)) *
        (n * Real.log n) := by
    have hsplit : 12 * (T : ℝ) / r * M m =
        (12 * (T : ℝ) / r * ((m : ℝ) * Real.log m)) * (M m / (m * Real.log m)) := by
      field_simp
    rw [hsplit]
    have hq : 0 ≤ M m / (m * Real.log m) := div_nonneg hM hLm.le
    calc _ ≤ (1728 * (1 / d + 1 / (2 * d ^ 2)) * ((n : ℝ) * Real.log n)) *
          (M m / (m * Real.log m)) := by gcongr
      _ = _ := by ring
  have hexp : (1728 * (1 / d + 1 / (2 * d ^ 2)) * (M m / (m * Real.log m)) + A) *
      (n * Real.log n) =
      1728 * (1 / d + 1 / (2 * d ^ 2)) * (M m / (m * Real.log m)) * (n * Real.log n) +
        A * n * Real.log n := by ring
  rw [hexp]
  linarith [hrec, hmain]

/-- The contraction coefficient of Corollary 5.5 is below `0.9998` once
`d ≥ 1729`. -/
theorem contraction_constant {d : ℕ} (hd : 1729 ≤ d) :
    (1728 / (d : ℝ)) * (1 + 1 / (2 * d)) ≤ 0.9998 := by
  have hd' : (1729 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hsq : (1729 : ℝ) * d ≤ d * d :=
    mul_le_mul_of_nonneg_right hd' hd0.le
  have heq : (1728 / (d : ℝ)) * (1 + 1 / (2 * d)) = 1728 * (2 * d + 1) / (2 * d ^ 2) := by
    field_simp
  rw [heq, div_le_iff₀ (by positivity)]
  nlinarith

/-- Theorem 1.1 in the abstract, with `d = 1729`: a cost satisfying (5.14)
with the stated parameter facts above `n₀`, and bounded by `B n log n` below
`n₀`, is `O(n log n)`. -/
theorem main_bound {M : ℕ → ℝ} {n₀ : ℕ} {T r p : ℕ → ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hn₀ : 2 ≤ n₀) (hM0 : ∀ n, 0 ≤ M n)
    (hparams : ∀ n, n₀ ≤ n →
      (T n : ℝ) * p n ≤ 48 * n ∧ 2 ≤ 3 * r n * p n ∧ 3 * r n * p n < n ∧ 0 < r n ∧
      Real.log (3 * (r n : ℝ) * p n) ≤
        (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n)
    (hrec : ∀ n, n₀ ≤ n →
      M n ≤ 12 * (T n : ℝ) / r n * M (3 * r n * p n) + A * n * Real.log n)
    (hbase : ∃ B, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < n₀ → M n ≤ B * n * Real.log n) :
    ∃ D, ∀ n, 2 ≤ n → M n ≤ D * n * Real.log n := by
  obtain ⟨B, hB, hbase⟩ := hbase
  have hρ : (1728 / (1729 : ℝ)) * (1 + 1 / (2 * 1729)) ≤ 0.9998 := by
    have := contraction_constant (d := 1729) le_rfl
    simpa using this
  refine mul_cost_of_contraction (f := fun n => 3 * r n * p n) (ρ := 0.9998) (C := A)
    (B := B) (by norm_num) (by norm_num) hA hB hn₀ ?_ ?_ hbase
  · intro n hn
    obtain ⟨_, h2, hlt, _, _⟩ := hparams n hn
    exact ⟨h2, hlt⟩
  · intro n hn
    obtain ⟨hTp, h2, hlt, hr, hlog⟩ := hparams n hn
    have hn2 : 2 ≤ n := le_trans hn₀ hn
    have hm : ((3 * r n * p n : ℕ) : ℝ) = 3 * r n * p n := by push_cast; ring
    have hlog' : Real.log ((3 * r n * p n : ℕ) : ℝ) ≤
        (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n := by
      rw [hm]
      exact hlog
    have hstep := normalised_step (M := M) (d := (1729 : ℝ)) hn2 hm h2 hTp hlog'
      (hrec n hn) (hM0 _) (by norm_num) hr
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
    have hm1 : (1 : ℝ) < ((3 * r n * p n : ℕ) : ℝ) := by exact_mod_cast h2
    have hL : 0 < (n : ℝ) * Real.log n := mul_pos (by linarith) (Real.log_pos hn1)
    have hLm : 0 < ((3 * r n * p n : ℕ) : ℝ) * Real.log ((3 * r n * p n : ℕ) : ℝ) :=
      mul_pos (by linarith) (Real.log_pos hm1)
    have hq : 0 ≤ M (3 * r n * p n) /
        (((3 * r n * p n : ℕ) : ℝ) * Real.log ((3 * r n * p n : ℕ) : ℝ)) :=
      div_nonneg (hM0 _) hLm.le
    have hstep' : M n / (n * Real.log n) ≤
        0.9998 * (M (3 * r n * p n) /
          (((3 * r n * p n : ℕ) : ℝ) * Real.log ((3 * r n * p n : ℕ) : ℝ))) + A := by
      calc M n / (n * Real.log n) ≤ _ := hstep
        _ ≤ _ := by gcongr
    rw [div_le_iff₀ hL] at hstep'
    calc M n ≤ _ := hstep'
      _ = _ := by
        field_simp

end IntegerMultBounds.NLogN
