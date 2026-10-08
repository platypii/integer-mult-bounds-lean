import IntegerMultBounds.NLogN.FFT
import IntegerMultBounds.NLogN.Approx

/-! The normalised radix-2 transform of Harvey and van der Hoeven, Lemma 3.2:
every butterfly halves, so the transform is a contraction, and an additive
error of norm at most `ε` injected into each output at each of the `n` levels
moves the result by at most `n * ε` elementwise. Proved over any normed
`ℂ`-space with abstract contractive twiddle maps (covering the synthetic ring
viewed coefficientwise), then over `ℂ` with the twiddles `ω ^ k`, where the
normalised transform is `2 ^ (-n)` times `fft` and hence `2 ^ (-n)` times the
quadratic transform when `ω ^ (2 ^ n) = 1`; finally packaged as an
`ApproxMap` with scaled error `n`. Twiddles are taken as exact, and no cost or
tape model is attached. -/

namespace IntegerMultBounds.NLogN

open Complex

theorem norm_half_complex : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Normalised decimation in time. `w m k` is the twiddle map at depth `m`
below the top level and output index `k`; the recursive calls shift the
family by one depth. -/
noncomputable def fftNorm : (n : ℕ) → (ℕ → ℕ → (V →L[ℂ] V)) → (Fin (2 ^ n) → V) → (Fin (2 ^ n) → V)
  | 0, _, a => a
  | n + 1, w, a =>
    let E := fftNorm n (fun m => w (m + 1)) (fun i => a (evenOddEquiv n (Sum.inl i)))
    let O := fftNorm n (fun m => w (m + 1)) (fun i => a (evenOddEquiv n (Sum.inr i)))
    fun k => (1 / 2 : ℂ) • (E (half n k) + w 0 k.val (O (half n k)))

/-- `fftNorm` with an additive error `e n k` injected into every output of the
level-`(n + 1)` combine step; both recursive calls reuse the same oracle. -/
noncomputable def fftNormErr : (n : ℕ) → (ℕ → ℕ → (V →L[ℂ] V)) → ((m : ℕ) → Fin (2 ^ (m + 1)) → V) →
    (Fin (2 ^ n) → V) → (Fin (2 ^ n) → V)
  | 0, _, _, a => a
  | n + 1, w, e, a =>
    let E := fftNormErr n (fun m => w (m + 1)) e (fun i => a (evenOddEquiv n (Sum.inl i)))
    let O := fftNormErr n (fun m => w (m + 1)) e (fun i => a (evenOddEquiv n (Sum.inr i)))
    fun k => (1 / 2 : ℂ) • (E (half n k) + w 0 k.val (O (half n k))) + e n k

/-- The normalised transform with contractive twiddles is a contraction. -/
theorem fftNorm_bound : ∀ (n : ℕ) (w : ℕ → ℕ → (V →L[ℂ] V)), (∀ m k, ‖w m k‖ ≤ 1) →
    ∀ (A : ℝ) (a : Fin (2 ^ n) → V), (∀ j, ‖a j‖ ≤ A) → ∀ k, ‖fftNorm n w a k‖ ≤ A
  | 0, _, _, A, a, hA, k => by simpa [fftNorm] using hA k
  | n + 1, w, hw, A, a, hA, k => by
    have hw' : ∀ m k, ‖w (m + 1) k‖ ≤ 1 := fun m k => hw (m + 1) k
    have hE := fftNorm_bound n (fun m => w (m + 1)) hw' A
      (fun i => a (evenOddEquiv n (Sum.inl i))) (fun i => hA _) (half n k)
    have hO := fftNorm_bound n (fun m => w (m + 1)) hw' A
      (fun i => a (evenOddEquiv n (Sum.inr i))) (fun i => hA _) (half n k)
    have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA k)
    simp only [fftNorm]
    rw [norm_smul, norm_half_complex]
    calc (1 / 2) * ‖_ + w 0 k.val _‖ ≤ (1 / 2) * (A + ‖w 0 k.val‖ * A) := by
          gcongr
          · exact norm_add_le _ _ |>.trans (by gcongr; exact (w 0 k.val).le_opNorm _ |>.trans (by gcongr))
      _ ≤ (1 / 2) * (A + 1 * A) := by gcongr; exact hw 0 k.val
      _ = A := by ring

/-- Linearity of the normalised transform in the input. -/
theorem fftNorm_sub : ∀ (n : ℕ) (w : ℕ → ℕ → (V →L[ℂ] V)) (x y : Fin (2 ^ n) → V)
    (k : Fin (2 ^ n)), fftNorm n w x k - fftNorm n w y k = fftNorm n w (fun j => x j - y j) k
  | 0, _, _, _, _ => by simp [fftNorm]
  | n + 1, w, x, y, k => by
    simp only [fftNorm]
    rw [← fftNorm_sub n, ← fftNorm_sub n, map_sub]
    simp only [smul_add, smul_sub]
    abel

/-- Elementwise error of the perturbed normalised transform: `n * ε` after
`n` levels. -/
theorem fftNormErr_sub_fftNorm : ∀ (n : ℕ) (w : ℕ → ℕ → (V →L[ℂ] V)), (∀ m k, ‖w m k‖ ≤ 1) →
    ∀ (ε : ℝ) (e : (m : ℕ) → Fin (2 ^ (m + 1)) → V), (∀ m k, ‖e m k‖ ≤ ε) →
    ∀ (a : Fin (2 ^ n) → V) (k : Fin (2 ^ n)),
      ‖fftNormErr n w e a k - fftNorm n w a k‖ ≤ n * ε
  | 0, _, _, ε, e, hε, a, k => by simp [fftNormErr, fftNorm]
  | n + 1, w, hw, ε, e, hε, a, k => by
    have hw' : ∀ m k, ‖w (m + 1) k‖ ≤ 1 := fun m k => hw (m + 1) k
    have hE := fftNormErr_sub_fftNorm n (fun m => w (m + 1)) hw' ε e hε
      (fun i => a (evenOddEquiv n (Sum.inl i))) (half n k)
    have hO := fftNormErr_sub_fftNorm n (fun m => w (m + 1)) hw' ε e hε
      (fun i => a (evenOddEquiv n (Sum.inr i))) (half n k)
    have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε n k)
    simp only [fftNormErr, fftNorm]
    have hid : ∀ (E' E O' O : V) (T : V →L[ℂ] V) (err : V),
        (1 / 2 : ℂ) • (E' + T O') + err - (1 / 2 : ℂ) • (E + T O)
          = (1 / 2 : ℂ) • ((E' - E) + T (O' - O)) + err := by
      intro E' E O' O T err
      rw [map_sub]
      simp only [smul_add, smul_sub]
      abel
    rw [hid]
    calc _ ≤ ‖(1 / 2 : ℂ) • (_ + w 0 k.val _)‖ + ‖e n k‖ := norm_add_le _ _
      _ ≤ (1 / 2) * (n * ε + ‖w 0 k.val‖ * (n * ε)) + ε := by
          rw [norm_smul, norm_half_complex]
          gcongr
          · exact norm_add_le _ _ |>.trans (by gcongr; exact (w 0 k.val).le_opNorm _ |>.trans (by gcongr))
          · exact hε n k
      _ ≤ (1 / 2) * (n * ε + 1 * (n * ε)) + ε := by gcongr; exact hw 0 k.val
      _ = (n + 1 : ℕ) * ε := by push_cast; ring

end Abstract

section Complex

/-- The twiddle family over `ℂ` for the root `ω`: at depth `m` the root is
`ω ^ (2 ^ m)`, so the twiddle at index `k` is multiplication by its `k`-th power. -/
noncomputable def twiddleFamily (ω : ℂ) (m k : ℕ) : ℂ →L[ℂ] ℂ :=
  ((ω ^ 2 ^ m) ^ k) • (1 : ℂ →L[ℂ] ℂ)

theorem twiddleFamily_apply (ω : ℂ) (m k : ℕ) (x : ℂ) :
    twiddleFamily ω m k x = (ω ^ 2 ^ m) ^ k * x := by
  simp [twiddleFamily]

theorem twiddleFamily_succ (ω : ℂ) :
    (fun m => twiddleFamily ω (m + 1)) = twiddleFamily (ω ^ 2) := by
  funext m k
  simp only [twiddleFamily]
  congr 2
  simp only [← pow_mul]
  ring_nf

theorem norm_twiddleFamily_le {ω : ℂ} (hω : ‖ω‖ = 1) (m k : ℕ) :
    ‖twiddleFamily ω m k‖ ≤ 1 := by
  unfold twiddleFamily
  rw [norm_smul, norm_pow, norm_pow, hω, one_pow, one_pow, one_mul]
  exact ContinuousLinearMap.norm_id_le

/-- The normalised transform over `ℂ` with root `ω`. -/
noncomputable def fftNormC (n : ℕ) (ω : ℂ) (a : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fftNorm n (twiddleFamily ω) a

/-- The perturbed normalised transform over `ℂ`. -/
noncomputable def fftNormCErr (n : ℕ) (ω : ℂ) (e : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ)
    (a : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fftNormErr n (twiddleFamily ω) e a

/-- The normalised transform is `2 ^ (-n)` times the unnormalised recursion. -/
theorem fftNormC_eq_fft : ∀ (n : ℕ) (ω : ℂ) (a : Fin (2 ^ n) → ℂ),
    fftNormC n ω a = fun k => (1 / 2 ^ n : ℂ) * fft n ω a k
  | 0, _, a => by funext k; simp [fftNormC, fftNorm, fft]
  | n + 1, ω, a => by
    funext k
    simp only [fftNormC, fftNorm, fft]
    rw [twiddleFamily_succ]
    have hE := congrFun (fftNormC_eq_fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inl i))))
      (half n k)
    have hO := congrFun (fftNormC_eq_fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inr i))))
      (half n k)
    simp only [fftNormC] at hE hO
    rw [hE, hO, twiddleFamily_apply, pow_zero, pow_one, smul_eq_mul]
    rw [pow_succ]
    field_simp
    ring

/-- With `ω ^ (2 ^ n) = 1`, the normalised transform is `2 ^ (-n)` times the
quadratic transform. -/
theorem fftNormC_eq_dftFin {n : ℕ} {ω : ℂ} (hω : ω ^ 2 ^ n = 1) (a : Fin (2 ^ n) → ℂ) :
    fftNormC n ω a = fun k => (1 / 2 ^ n : ℂ) * dftFin ω a k := by
  rw [fftNormC_eq_fft, fft_eq_dftFin n ω hω]

theorem fftNormC_bound {n : ℕ} {ω : ℂ} (hω : ‖ω‖ = 1) {A : ℝ} {a : Fin (2 ^ n) → ℂ}
    (hA : ∀ j, ‖a j‖ ≤ A) (k : Fin (2 ^ n)) : ‖fftNormC n ω a k‖ ≤ A :=
  fftNorm_bound n _ (norm_twiddleFamily_le hω) A a hA k

theorem fftNormCErr_sub {n : ℕ} {ω : ℂ} (hω : ‖ω‖ = 1) {ε : ℝ}
    {e : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ} (hε : ∀ m k, ‖e m k‖ ≤ ε)
    (a : Fin (2 ^ n) → ℂ) (k : Fin (2 ^ n)) :
    ‖fftNormCErr n ω e a k - fftNormC n ω a k‖ ≤ n * ε :=
  fftNormErr_sub_fftNorm n _ (norm_twiddleFamily_le hω) ε e hε a k

/-- The exact normalised transform as a continuous linear map. -/
noncomputable def fftNormCLM (n : ℕ) (ω : ℂ) : (Fin (2 ^ n) → ℂ) →L[ℂ] (Fin (2 ^ n) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    ∑ j, ((1 / 2 ^ n : ℂ) * ω ^ (j.val * k.val)) • ContinuousLinearMap.proj j

theorem fftNormCLM_apply {n : ℕ} {ω : ℂ} (hω : ω ^ 2 ^ n = 1) (a : Fin (2 ^ n) → ℂ) :
    fftNormCLM n ω a = fftNormC n ω a := by
  rw [fftNormC_eq_dftFin hω]
  funext k
  simp only [fftNormCLM, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dftFin,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Lemma 3.2 over `ℂ`: the perturbed normalised transform with per-step
error at most `2 ^ (-p)` is an approximation of scaled error `n = log₂ N`. -/
theorem approxMap_fftNormC {n p : ℕ} {ω : ℂ} (hω : ‖ω‖ = 1) (hω1 : ω ^ 2 ^ n = 1)
    {e : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ} (he : ∀ m k, ‖e m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (fftNormCErr n ω e) (fftNormCLM n ω) n := by
  intro a _
  rw [fftNormCLM_apply hω1]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : ‖fftNormCErr n ω e a - fftNormC n ω a‖ ≤ n * (1 / 2 ^ p) := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    exact fftNormCErr_sub hω he a k
  calc (2 : ℝ) ^ p * ‖fftNormCErr n ω e a - fftNormC n ω a‖
      ≤ 2 ^ p * (n * (1 / 2 ^ p)) := by gcongr
    _ = n := by field_simp

end Complex

end IntegerMultBounds.NLogN
