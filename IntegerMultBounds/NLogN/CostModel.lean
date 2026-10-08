import IntegerMultBounds.NLogN.SynthMultiD
import IntegerMultBounds.NLogN.MainParams

/-! An operation-count model for the power-of-two transforms of Section 3 of
Harvey–van der Hoeven and for the convolution pipeline built from them.

The counts are of elementary fixed-point operations on `p`-bit words and of
synthetic-ring pointwise products, each delegated to four integer
multiplications of `3rp`-bit numbers (Lemma 2.5). `synthFFTOps` mirrors the
recursion of `fftNorm` (two half-size calls plus one butterfly per output,
each butterfly costing `2r` word operations; the shift twiddles are free data
moves). `synthDFTDOps` applies each one-dimensional transform to every slice,
as in the coordinate splitting `synthDFTD_succ`. The pipeline count is three
transforms, the pointwise products, and `O(rp)` overhead per product.

Proved: closed forms and the bounds `O(r t log t)`, `O(r T log T)`,
`(4T/r) M(3rp) + O(T p log T)`, and, with the Section 5 parameters, the
recursive-step bound `3 · pipeline ≤ (12T/r) M(3rp) + 2880 n log₂ n`.

Not modelled: tape steps, data rearrangement, the cost of computing the chirp
and Gaussian weights, and any link between these counts and the machine
model. -/

namespace IntegerMultBounds.NLogN

/-! ### One-dimensional synthetic FFT -/

/-- Word operations of the normalized radix-2 synthetic transform of length
`2^n` over `ℂ[y]/(y^r+1)`, mirroring `fftNorm`: two recursive calls, then one
butterfly (an `r`-coordinate addition and an `r`-coordinate halving) per
output. -/
def synthFFTOps (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * synthFFTOps r n + 2 ^ (n + 1) * (2 * r)

theorem synthFFTOps_zero (r : ℕ) : synthFFTOps r 0 = 0 := rfl

theorem synthFFTOps_succ (r n : ℕ) :
    synthFFTOps r (n + 1) = 2 * synthFFTOps r n + 2 ^ (n + 1) * (2 * r) := rfl

/-- Closed form: `2 r t log₂ t` for `t = 2^n`. -/
theorem synthFFTOps_eq (r n : ℕ) : synthFFTOps r n = n * 2 ^ n * (2 * r) := by
  induction n with
  | zero => simp [synthFFTOps]
  | succ n ih =>
    rw [synthFFTOps_succ, ih]
    ring

theorem synthFFTOps_le (r n : ℕ) : synthFFTOps r n ≤ 4 * r * 2 ^ n * n := by
  rw [synthFFTOps_eq]
  calc n * 2 ^ n * (2 * r) = 2 * (r * 2 ^ n * n) := by ring
    _ ≤ 4 * (r * 2 ^ n * n) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * r * 2 ^ n * n := by ring

/-! ### Multidimensional synthetic transform -/

/-- Word operations of the `d`-dimensional synthetic transform of sizes
`2^(e i)`: for each coordinate, one length-`2^(e i)` transform on each of the
`T / 2^(e i)` slices. -/
def synthDFTDOps {d : ℕ} (r : ℕ) (e : Fin d → ℕ) : ℕ :=
  ∑ i, (∏ j, 2 ^ e j) / 2 ^ e i * synthFFTOps r (e i)

theorem synthDFTDOps_eq {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    synthDFTDOps r e = 2 * r * (∏ j, 2 ^ e j) * ∑ i, e i := by
  unfold synthDFTDOps
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [synthFFTOps_eq]
  obtain ⟨c, hc⟩ : 2 ^ e i ∣ ∏ j, 2 ^ e j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [hc, Nat.mul_div_cancel_left _ (by positivity)]
  ring

theorem synthDFTDOps_le {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    synthDFTDOps r e ≤ 4 * r * (∏ j, 2 ^ e j) * ∑ i, e i := by
  rw [synthDFTDOps_eq]
  calc 2 * r * (∏ j, 2 ^ e j) * ∑ i, e i = 2 * (r * (∏ j, 2 ^ e j) * ∑ i, e i) := by ring
    _ ≤ 4 * (r * (∏ j, 2 ^ e j) * ∑ i, e i) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * r * (∏ j, 2 ^ e j) * ∑ i, e i := by ring

/-- `O(r T log₂ T)` with `T = 2^(∑ e i)`. -/
theorem synthDFTDOps_le_log {d : ℕ} (r : ℕ) (e : Fin d → ℕ) :
    synthDFTDOps r e ≤ 4 * r * 2 ^ (∑ i, e i) * ∑ i, e i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact synthDFTDOps_le r e

/-! ### The convolution pipeline over the synthetic ring -/

/-- Operations of the Proposition 3.4 pipeline: three transforms (two forward,
one inverse) on `p`-bit words, then `T' = ∏ 2^(e i)` pointwise products, each
four integer multiplications of `3rp`-bit numbers (`Mcost (3 r p)` each) plus
`4rp` words of overhead for the final scaling. -/
def pipelineOps {d : ℕ} (r p : ℕ) (e : Fin d → ℕ) (Mcost : ℕ → ℕ) : ℕ :=
  3 * synthDFTDOps r e * p + (∏ i, 2 ^ e i) * (4 * Mcost (3 * r * p) + 4 * r * p)

theorem pipelineOps_le {d : ℕ} (r p : ℕ) (e : Fin d → ℕ) (Mcost : ℕ → ℕ) :
    pipelineOps r p e Mcost ≤
      (∏ i, 2 ^ e i) * (4 * Mcost (3 * r * p) + 4 * r * p + 12 * r * p * ∑ i, e i) := by
  unfold pipelineOps
  rw [synthDFTDOps_eq]
  nlinarith [Nat.zero_le (r * (∏ j, 2 ^ e j) * (∑ i, e i) * p)]

/-- The paper's shape `(4T/r) M(3rp) + O(T p log T)` with `T = r T'`. -/
theorem pipelineOps_le' {d : ℕ} (r p : ℕ) (e : Fin d → ℕ) (Mcost : ℕ → ℕ) :
    pipelineOps r p e Mcost ≤
      4 * (∏ i, 2 ^ e i) * Mcost (3 * r * p) +
        4 * (r * ∏ i, 2 ^ e i) * p * (1 + 3 * ∑ i, e i) := by
  calc pipelineOps r p e Mcost
      ≤ (∏ i, 2 ^ e i) * (4 * Mcost (3 * r * p) + 4 * r * p + 12 * r * p * ∑ i, e i) :=
        pipelineOps_le r p e Mcost
    _ = 4 * (∏ i, 2 ^ e i) * Mcost (3 * r * p) +
        4 * (r * ∏ i, 2 ^ e i) * p * (1 + 3 * ∑ i, e i) := by ring

/-! ### The recursive step with the Section 5 parameters -/

/-- Three pipeline invocations (Proposition 5.3) with `r = rootSize`,
`p = precision = 6b`, and a factorization `r · ∏ 2^(e i) = T` cost at most
`12 T' · M(3rp) + 2880 n log₂ n` with `T' = T / r`. -/
theorem main_ops_le {d n k : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (e : Fin k → ℕ)
    (hT : rootSize d n * ∏ i, 2 ^ e i = transformSize n) (Mcost : ℕ → ℕ) :
    3 * pipelineOps (rootSize d n) (precision n) e Mcost ≤
      12 * (∏ i, 2 ^ e i) * Mcost (3 * rootSize d n * precision n) +
        2880 * n * Nat.log 2 n := by
  have hb : 4096 ≤ chunkSize n := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))
      _ ≤ n := hn
  have hTb : transformSize n * chunkSize n < 8 * n := (transformSize_bounds hn2).2
  have hTn : transformSize n < n := transformSize_lt hn2 (by omega)
  have hnb : n ≤ 2 ^ chunkSize n := n_le_two_pow_chunk n
  have hP : ∏ i, 2 ^ e i = 2 ^ ∑ i, e i := Finset.prod_pow_eq_pow_sum _ _ _
  have hr1 : 1 ≤ rootSize d n := Nat.one_le_two_pow
  have hPT : ∏ i, 2 ^ e i ≤ transformSize n := by
    rw [← hT]
    exact Nat.le_mul_of_pos_left _ hr1
  have hLb : ∑ i, e i ≤ chunkSize n := by
    have : 2 ^ ∑ i, e i < 2 ^ chunkSize n := by rw [← hP]; omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this |>.le
  have hlog : chunkSize n ≤ 2 * Nat.log 2 n := by
    have h1 := chunkSize_le_log_succ n
    have h2 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn2
    omega
  have hp : precision n = 6 * chunkSize n := rfl
  unfold pipelineOps
  rw [synthDFTDOps_eq]
  have key : 3 * (3 * (2 * rootSize d n * (∏ j, 2 ^ e j) * ∑ i, e i) * precision n +
      (∏ i, 2 ^ e i) * (4 * Mcost (3 * rootSize d n * precision n) +
        4 * rootSize d n * precision n)) =
      12 * (∏ i, 2 ^ e i) * Mcost (3 * rootSize d n * precision n) +
        (18 * (∑ i, e i) * precision n + 12 * precision n) * (rootSize d n * ∏ i, 2 ^ e i) := by
    ring
  rw [key, hT]
  apply Nat.add_le_add_left
  have h1 : (∑ i, e i) * precision n ≤ chunkSize n * precision n :=
    Nat.mul_le_mul_right _ hLb
  have h2 : precision n ≤ chunkSize n * precision n := Nat.le_mul_of_pos_left _ (by omega)
  calc (18 * (∑ i, e i) * precision n + 12 * precision n) * transformSize n
      ≤ (30 * (chunkSize n * precision n)) * transformSize n := by
        apply Nat.mul_le_mul_right
        nlinarith [h1, h2]
    _ = 180 * (transformSize n * chunkSize n) * chunkSize n := by rw [hp]; ring
    _ ≤ 180 * (8 * n) * chunkSize n := by gcongr
    _ = 1440 * n * chunkSize n := by ring
    _ ≤ 1440 * n * (2 * Nat.log 2 n) := by gcongr
    _ = 2880 * n * Nat.log 2 n := by ring

/-- The same bound in the paper's form `(12T/r) M(3rp) + O(n log n)`. -/
theorem main_ops_le' {d n k : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) (e : Fin k → ℕ)
    (hT : rootSize d n * ∏ i, 2 ^ e i = transformSize n) (Mcost : ℕ → ℕ) :
    3 * pipelineOps (rootSize d n) (precision n) e Mcost ≤
      (12 * transformSize n / rootSize d n) * Mcost (3 * rootSize d n * precision n) +
        2880 * n * Nat.log 2 n := by
  have hr : 0 < rootSize d n := pow_pos (by norm_num) _
  have hdiv : 12 * transformSize n / rootSize d n = 12 * ∏ i, 2 ^ e i := by
    rw [← hT, show 12 * (rootSize d n * ∏ i, 2 ^ e i) = rootSize d n * (12 * ∏ i, 2 ^ e i) by
      ring]
    exact Nat.mul_div_cancel_left _ hr
  rw [hdiv]
  exact main_ops_le hd hn e hT Mcost

end IntegerMultBounds.NLogN
