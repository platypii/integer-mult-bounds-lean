import IntegerMultBounds.NLogN.FFT
import Mathlib.Analysis.Complex.Basic

/-! Rounding-error analysis of the radix-2 transform over `ℂ`. Each output at
each level of the recursion is perturbed by an explicit error term of norm at
most `ε`; the computed transform then differs from the exact one by at most
`(2 ^ n - 1) * ε` elementwise when `‖ω‖ = 1`, and the exact transform grows by
at most the factor `2 ^ n`. A complex value within `1 / 2` of an integer rounds
to it, so integer vectors are recovered exactly from close approximations.
This fixes no precision, and does not compile fixed-point arithmetic to tape
steps or bound the error of the full forward–pointwise–inverse pipeline. -/

namespace IntegerMultBounds.NLogN

open Complex

/-- `fft` with an additive error `e n k` injected into every output of the
level-`(n + 1)` combine step. The same oracle `e` is reused by both recursive
calls, which is harmless for an upper bound under `∀ m k, ‖e m k‖ ≤ ε`. -/
def fftErr : (n : ℕ) → ℂ → ((m : ℕ) → Fin (2 ^ (m + 1)) → ℂ) →
    (Fin (2 ^ n) → ℂ) → (Fin (2 ^ n) → ℂ)
  | 0, _, _, a => a
  | n + 1, ω, e, a =>
    let E := fftErr n (ω ^ 2) e (fun i => a (evenOddEquiv n (Sum.inl i)))
    let O := fftErr n (ω ^ 2) e (fun i => a (evenOddEquiv n (Sum.inr i)))
    fun k => E (half n k) + ω ^ k.val * O (half n k) + e n k

theorem norm_pow_eq_one {ω : ℂ} (hω : ‖ω‖ = 1) (k : ℕ) : ‖ω ^ k‖ = 1 := by
  rw [norm_pow, hω, one_pow]

/-- Growth of the exact transform. -/
theorem fft_bound : ∀ (n : ℕ) (ω : ℂ), ‖ω‖ = 1 → ∀ (A : ℝ) (a : Fin (2 ^ n) → ℂ),
    (∀ j, ‖a j‖ ≤ A) → ∀ k, ‖fft n ω a k‖ ≤ 2 ^ n * A
  | 0, _, _, A, a, hA, k => by
    simpa [fft] using hA k
  | n + 1, ω, hω, A, a, hA, k => by
    have hω2 : ‖ω ^ 2‖ = 1 := norm_pow_eq_one hω 2
    have hE := fft_bound n (ω ^ 2) hω2 A (fun i => a (evenOddEquiv n (Sum.inl i)))
      (fun i => hA _) (half n k)
    have hO := fft_bound n (ω ^ 2) hω2 A (fun i => a (evenOddEquiv n (Sum.inr i)))
      (fun i => hA _) (half n k)
    simp only [fft]
    calc _ ≤ ‖fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inl i))) (half n k)‖ +
          ‖ω ^ k.val * fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inr i))) (half n k)‖ :=
          norm_add_le _ _
      _ ≤ 2 ^ n * A + 1 * (2 ^ n * A) := by
          rw [norm_mul, norm_pow_eq_one hω]
          exact add_le_add hE (by linarith)
      _ = 2 ^ (n + 1) * A := by ring

/-- Elementwise error of the perturbed transform. -/
theorem fftErr_sub_fft : ∀ (n : ℕ) (ω : ℂ), ‖ω‖ = 1 →
    ∀ (ε : ℝ) (e : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ), (∀ m k, ‖e m k‖ ≤ ε) →
    ∀ (a : Fin (2 ^ n) → ℂ) (k : Fin (2 ^ n)),
      ‖fftErr n ω e a k - fft n ω a k‖ ≤ (2 ^ n - 1) * ε
  | 0, _, _, ε, e, hε, a, k => by
    have h0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε 0 ⟨0, by positivity⟩)
    simp [fftErr, fft]
  | n + 1, ω, hω, ε, e, hε, a, k => by
    have hω2 : ‖ω ^ 2‖ = 1 := norm_pow_eq_one hω 2
    have hE := fftErr_sub_fft n (ω ^ 2) hω2 ε e hε
      (fun i => a (evenOddEquiv n (Sum.inl i))) (half n k)
    have hO := fftErr_sub_fft n (ω ^ 2) hω2 ε e hε
      (fun i => a (evenOddEquiv n (Sum.inr i))) (half n k)
    have he := hε n k
    simp only [fftErr, fft]
    set E1 := fftErr n (ω ^ 2) e (fun i => a (evenOddEquiv n (Sum.inl i))) (half n k)
    set O1 := fftErr n (ω ^ 2) e (fun i => a (evenOddEquiv n (Sum.inr i))) (half n k)
    set E := fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inl i))) (half n k)
    set O := fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inr i))) (half n k)
    have hsplit : E1 + ω ^ k.val * O1 + e n k - (E + ω ^ k.val * O) =
        (E1 - E) + ω ^ k.val * (O1 - O) + e n k := by ring
    rw [hsplit]
    calc _ ≤ ‖(E1 - E) + ω ^ k.val * (O1 - O)‖ + ‖e n k‖ := norm_add_le _ _
      _ ≤ ‖E1 - E‖ + ‖ω ^ k.val * (O1 - O)‖ + ‖e n k‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (2 ^ n - 1) * ε + 1 * ((2 ^ n - 1) * ε) + ε := by
          rw [norm_mul, norm_pow_eq_one hω]
          exact add_le_add (add_le_add hE (by linarith)) he
      _ = (2 ^ (n + 1) - 1) * ε := by ring

/-- With errors at most `2 ^ (-p)`, the transform error is below `2 ^ n / 2 ^ p`. -/
theorem fftErr_sub_fft_pow (n : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) (p : ℕ)
    (e : (m : ℕ) → Fin (2 ^ (m + 1)) → ℂ) (he : ∀ m k, ‖e m k‖ ≤ 1 / 2 ^ p)
    (a : Fin (2 ^ n) → ℂ) (k : Fin (2 ^ n)) :
    ‖fftErr n ω e a k - fft n ω a k‖ ≤ 2 ^ n / 2 ^ p := by
  have h := fftErr_sub_fft n ω hω (1 / 2 ^ p) e he a k
  have hp : (0 : ℝ) < 1 / 2 ^ p := by positivity
  calc _ ≤ ((2 : ℝ) ^ n - 1) * (1 / 2 ^ p) := h
    _ ≤ 2 ^ n * (1 / 2 ^ p) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        linarith
    _ = 2 ^ n / 2 ^ p := by ring

/-- A complex value within `1 / 2` of an integer rounds to that integer. -/
theorem round_exact {z : ℂ} {c : ℤ} (h : ‖z - c‖ < 1 / 2) : round z.re = c := by
  have hre : |z.re - c| < 1 / 2 := by
    have := abs_re_le_norm (z - c)
    simp only [sub_re, intCast_re] at this
    linarith
  rw [round_eq_iff, Set.mem_Ico]
  rw [abs_lt] at hre
  constructor <;> linarith [hre.1, hre.2]

/-- Error of a pointwise product of approximations. -/
theorem mul_err (x x' y y' : ℂ) :
    ‖x' * y' - x * y‖ ≤ ‖x' - x‖ * ‖y‖ + ‖x‖ * ‖y' - y‖ + ‖x' - x‖ * ‖y' - y‖ := by
  have hsplit : x' * y' - x * y = (x' - x) * y + x * (y' - y) + (x' - x) * (y' - y) := by
    ring
  rw [hsplit]
  calc _ ≤ ‖(x' - x) * y + x * (y' - y)‖ + ‖(x' - x) * (y' - y)‖ := norm_add_le _ _
    _ ≤ ‖(x' - x) * y‖ + ‖x * (y' - y)‖ + ‖(x' - x) * (y' - y)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [norm_mul, norm_mul, norm_mul]

/-- Integer vectors are recovered exactly from approximations within `1 / 2`. -/
theorem recover_of_close {N : ℕ} (c : Fin N → ℤ) (z : Fin N → ℂ)
    (h : ∀ k, ‖z k - c k‖ < 1 / 2) : (fun k => round (z k).re) = c := by
  funext k
  exact round_exact (h k)

end IntegerMultBounds.NLogN
