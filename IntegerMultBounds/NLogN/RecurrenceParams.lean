import IntegerMultBounds.NLogN.MainParams
import IntegerMultBounds.NLogN.MainRecurrence
import IntegerMultBounds.NLogN.CostModel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The parameter facts behind Corollary 5.5 and Theorem 1.1 of Harvey and
van der Hoeven: with `T`, `r`, `p` the Section 5.1 parameters and
`n ≥ 2^(d^12)`, `T p ≤ 48 n`, `3 r p < n`, and
`log (3rp) ≤ (1/d + 1/(2d²)) log n`. At `d = 1729` these are exactly the
hypotheses of `main_bound`, so any cost satisfying the recursive inequality
`M(n) ≤ (12T/r) M(3rp) + A n log n` above `2^(1729^12)` is `O(n log n)`. The
recursive inequality itself is still a hypothesis. -/

namespace IntegerMultBounds.NLogN

/-- `T p ≤ 48 n`, from `T b < 8n` and `p = 6b`. -/
theorem Tp_le {n : ℕ} (hn : 2 ≤ n) :
    (transformSize n : ℝ) * precision n ≤ 48 * n := by
  have h := (transformSize_bounds hn).2
  have h' : transformSize n * precision n ≤ 48 * n := by
    unfold precision
    calc transformSize n * (6 * chunkSize n) = 6 * (transformSize n * chunkSize n) := by ring
      _ ≤ 6 * (8 * n) := Nat.mul_le_mul_left _ h.le
      _ = 48 * n := by ring
  exact_mod_cast h'

theorem rootSize_pos (d n : ℕ) : 0 < rootSize d n := by
  unfold rootSize; positivity

/-- Stated with a variable base so the kernel never evaluates `2^(1729^12)`. -/
theorem two_le_two_pow_pow {d : ℕ} (hd : 1 ≤ d) : 2 ≤ 2 ^ (d ^ 12) :=
  Nat.le_self_pow (by positivity) 2

theorem three_rp_ge_two {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    2 ≤ 3 * rootSize d n * precision n := by
  have hr := rootSize_pos d n
  have hp := precision_ge hd hn
  nlinarith

/-- `10368 b ≤ 2^(b−1)` for `b ≥ 20`. -/
theorem mul_le_two_pow_pred {b : ℕ} (hb : 20 ≤ b) : 10368 * b ≤ 2 ^ (b - 1) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    have h1 : 2 ^ (b + 1 - 1) = 2 * 2 ^ (b - 1) := by
      rw [show b + 1 - 1 = (b - 1) + 1 by omega, pow_succ]; ring
    have h2 : 10368 ≤ 2 ^ (b - 1) := by
      calc 10368 ≤ 2 ^ 19 := by norm_num
        _ ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `2^(b−1) ≤ n` where `b = ⌈log₂ n⌉`. -/
theorem two_pow_pred_chunk_le {n : ℕ} (hn : 2 ≤ n) : 2 ^ (chunkSize n - 1) ≤ n := by
  have h := two_pow_chunk_lt hn
  have hb : 1 ≤ chunkSize n := Nat.clog_pos (by norm_num) (by omega)
  have : 2 ^ chunkSize n = 2 * 2 ^ (chunkSize n - 1) := by
    rw [← pow_succ']; exact congrArg _ (by omega)
  omega

/-- `3 r p < n`: the recursive size is smaller than the input. -/
theorem three_rp_lt {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    3 * rootSize d n * precision n < n := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hb4096 := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n := by
    calc 2 ≤ 2 ^ ((e + 1) ^ 12) :=
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ ((e + 1) ^ 12) :=
                Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))
      _ ≤ n := hn
  have hr := (rootSize_pow_bounds (d := e + 1) (n := n) (by omega)).2
  have hT := (transformSize_bounds hn2).2
  have hnb : 10368 * chunkSize n ≤ n :=
    le_trans (mul_le_two_pow_pred (by omega)) (two_pow_pred_chunk_le hn2)
  set b := chunkSize n with hb'
  set T := transformSize n with hT'
  set r := rootSize (e + 1) n with hr'
  have hp : precision n = 6 * b := rfl
  rw [hp]
  have hb0 : 0 < b := by omega
  have h288 : 288 * ((18 * b) ^ e * 2 ^ e) ≤ (10368 * b) ^ e := by
    rw [← mul_pow]
    calc 288 * (18 * b * 2) ^ e ≤ 288 ^ e * (18 * b * 2) ^ e :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 288)
      _ = (10368 * b) ^ e := by rw [← mul_pow]; congr 1; ring
  have key : (3 * r * (6 * b)) ^ (e + 1) * b < n ^ (e + 1) * b := by
    calc (3 * r * (6 * b)) ^ (e + 1) * b
        = ((18 * b) ^ (e + 1) * b) * r ^ (e + 1) := by ring
      _ < ((18 * b) ^ (e + 1) * b) * (2 ^ (e + 1) * T) :=
          mul_lt_mul_of_pos_left hr (Nat.mul_pos (pow_pos (by omega) _) hb0)
      _ = (36 * ((18 * b) ^ e * 2 ^ e)) * (T * b) * b := by ring
      _ ≤ (36 * ((18 * b) ^ e * 2 ^ e)) * (8 * n) * b :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT.le)
      _ = (288 * ((18 * b) ^ e * 2 ^ e)) * (b * n) := by ring
      _ ≤ (10368 * b) ^ e * (b * n) := Nat.mul_le_mul_right _ h288
      _ ≤ n ^ e * (b * n) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnb e)
      _ = n ^ (e + 1) * b := by ring
  have := Nat.lt_of_mul_lt_mul_right key
  exact (Nat.pow_lt_pow_iff_left (by omega)).1 this

/-- The sixth root of `b` as a real number, with `c^6 = b`, `c ≥ 4`, and `d² ≤ c`. -/
theorem exists_sixth_root {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    ∃ c : ℝ, 0 ≤ c ∧ c ^ 6 = (chunkSize n : ℝ) ∧ 4 ≤ c ∧ ((d : ℝ) ^ 2) ≤ c := by
  have hb := chunkSize_ge hn
  have hb4 := chunkSize_ge_4096 hd hn
  set b := chunkSize n with hb'
  have hb0 : (0 : ℝ) ≤ b := by positivity
  refine ⟨(b : ℝ) ^ ((1 : ℝ) / 6), Real.rpow_nonneg hb0 _, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast ((b : ℝ) ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul hb0]; norm_num
  · have h : (4 : ℝ) ^ 6 ≤ ((b : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 := by
      rw [← Real.rpow_natCast ((b : ℝ) ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul hb0]; norm_num
      exact_mod_cast hb4
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg hb0 _) (by norm_num)).1 h
  · have h : ((d : ℝ) ^ 2) ^ 6 ≤ ((b : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 := by
      rw [← Real.rpow_natCast ((b : ℝ) ^ ((1 : ℝ) / 6)) 6, ← Real.rpow_mul hb0]; norm_num
      rw [← pow_mul]; exact_mod_cast hb
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hb0 _) (by norm_num)).1 h

/-- `2 d² (log 36 + log b) ≤ (b − 1) log 2`: the slack of Corollary 5.5. -/
theorem two_d_sq_log_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    2 * (d : ℝ) ^ 2 * (Real.log 36 + Real.log (chunkSize n)) ≤
      ((chunkSize n : ℝ) - 1) * Real.log 2 := by
  obtain ⟨c, hc0, hc6, hc4, hdc⟩ := exists_sixth_root hd hn
  have hlog36 : Real.log 36 ≤ 35 := by
    have := Real.log_le_sub_one_of_pos (x := 36) (by norm_num); linarith
  have hlogb : Real.log (chunkSize n) ≤ 6 * c := by
    rw [← hc6, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (x := c) (by linarith)
    push_cast; linarith
  have hlog2 := Real.log_two_gt_d9
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  have hl36 : 0 ≤ Real.log 36 := Real.log_nonneg (by norm_num)
  have hlb : 0 ≤ Real.log (chunkSize n) := Real.log_nonneg (by
    have := chunkSize_ge_4096 hd hn; exact_mod_cast (show 1 ≤ chunkSize n by omega))
  have h1 : 2 * (d : ℝ) ^ 2 * (Real.log 36 + Real.log (chunkSize n)) ≤ 2 * c * (35 + 6 * c) := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hc2 : 16 ≤ c ^ 2 := by nlinarith
  have hc4' : 256 ≤ c ^ 4 := by nlinarith
  have hc6' : 256 * c ^ 2 ≤ c ^ 6 := by nlinarith
  calc 2 * (d : ℝ) ^ 2 * (Real.log 36 + Real.log (chunkSize n))
      ≤ 2 * c * (35 + 6 * c) := h1
    _ ≤ (c ^ 6 - 1) * 0.6931471803 := by nlinarith
    _ ≤ (c ^ 6 - 1) * Real.log 2 := by
        apply mul_le_mul_of_nonneg_left hlog2.le; nlinarith
    _ = ((chunkSize n : ℝ) - 1) * Real.log 2 := by rw [hc6]

/-- `log (3 r p) ≤ (1/d + 1/(2d²)) log n`, the Corollary 5.5 estimate. -/
theorem log_three_rp_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    Real.log (3 * (rootSize d n : ℝ) * precision n) ≤
      (1 / (d : ℝ) + 1 / (2 * (d : ℝ) ^ 2)) * Real.log n := by
  have hb4096 := chunkSize_ge_4096 hd hn
  have hn2 : 2 ≤ n := by
    calc 2 ≤ 2 ^ (d ^ 12) :=
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))
      _ ≤ n := hn
  have hTn := transformSize_lt hn2 (by omega)
  have hr := (rootSize_pow_bounds (d := d) (n := n) (by omega)).2
  have hrn : rootSize d n ^ d < 2 ^ d * n := by
    calc rootSize d n ^ d < 2 ^ d * transformSize n := hr
      _ ≤ 2 ^ d * n := Nat.mul_le_mul_left _ hTn.le
  have hrnR : ((rootSize d n : ℝ)) ^ d < 2 ^ d * n := by exact_mod_cast hrn
  have hrpos : (0 : ℝ) < rootSize d n := by exact_mod_cast rootSize_pos d n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hbpos : (0 : ℝ) < chunkSize n := by exact_mod_cast (show 0 < chunkSize n by omega)
  -- `d log r < d log 2 + log n`
  have hlogr : (d : ℝ) * Real.log (rootSize d n) < (d : ℝ) * Real.log 2 + Real.log n := by
    have := Real.log_lt_log (pow_pos hrpos d) hrnR
    rwa [Real.log_pow, Real.log_mul (by positivity) hnpos.ne', Real.log_pow] at this
  have hlogr' : Real.log (rootSize d n) < Real.log 2 + Real.log n / d := by
    have h2 : (d : ℝ) * (Real.log 2 + Real.log n / d) = d * Real.log 2 + Real.log n := by
      field_simp
    have h := hlogr
    rw [← h2] at h
    exact lt_of_mul_lt_mul_left h hdpos.le
  -- `log (3 r p) = log 3 + log r + log 6 + log b`
  have hp : (precision n : ℝ) = 6 * chunkSize n := by unfold precision; push_cast; ring
  have hsplit : Real.log (3 * (rootSize d n : ℝ) * precision n) =
      Real.log 3 + Real.log (rootSize d n) + (Real.log 6 + Real.log (chunkSize n)) := by
    rw [hp, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hrpos.ne',
      Real.log_mul (by norm_num) hbpos.ne']
  have hlog36 : Real.log 3 + Real.log 2 + Real.log 6 = Real.log 36 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  -- `log n ≥ (b − 1) log 2`
  have hlogn : ((chunkSize n : ℝ) - 1) * Real.log 2 ≤ Real.log n := by
    have h := two_pow_pred_chunk_le hn2
    have hR : ((2 : ℝ)) ^ (chunkSize n - 1) ≤ n := by exact_mod_cast h
    have := Real.log_le_log (by positivity) hR
    rw [Real.log_pow] at this
    have hcast : ((chunkSize n - 1 : ℕ) : ℝ) = (chunkSize n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at this; exact this
  have hslack := two_d_sq_log_le hd hn
  have hd2 : (0 : ℝ) < 2 * (d : ℝ) ^ 2 := by positivity
  have hmain : Real.log 36 + Real.log (chunkSize n) ≤ Real.log n / (2 * (d : ℝ) ^ 2) := by
    rw [le_div_iff₀ hd2]; nlinarith
  calc Real.log (3 * (rootSize d n : ℝ) * precision n)
      = Real.log 3 + Real.log (rootSize d n) + (Real.log 6 + Real.log (chunkSize n)) := hsplit
    _ ≤ Real.log 3 + (Real.log 2 + Real.log n / d) + (Real.log 6 + Real.log (chunkSize n)) := by
        linarith
    _ = (Real.log 36 + Real.log (chunkSize n)) + Real.log n / d := by rw [← hlog36]; ring
    _ ≤ Real.log n / (2 * (d : ℝ) ^ 2) + Real.log n / d := by linarith
    _ = (1 / (d : ℝ) + 1 / (2 * (d : ℝ) ^ 2)) * Real.log n := by ring

/-- The hypotheses of `main_bound` at `d = 1729`. -/
theorem recurrence_params {n : ℕ} (hn : 2 ^ (1729 ^ 12) ≤ n) :
    (transformSize n : ℝ) * precision n ≤ 48 * n ∧
      2 ≤ 3 * rootSize 1729 n * precision n ∧ 3 * rootSize 1729 n * precision n < n ∧
      0 < rootSize 1729 n ∧
      Real.log (3 * (rootSize 1729 n : ℝ) * precision n) ≤
        (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hn2 : 2 ≤ n := le_trans (two_le_two_pow_pow (d := 1729) (by norm_num)) hn
  refine ⟨Tp_le hn2, three_rp_ge_two hd hn, three_rp_lt hd hn, rootSize_pos _ _, ?_⟩
  have := log_three_rp_le hd hn
  simpa using this

/-- Theorem 1.1 for the Section 5.1 parameters: any cost satisfying the recursive
inequality above `2^(1729^12)` is `O(n log n)`. -/
theorem n_log_n_of_rec {M : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hM0 : ∀ n, 0 ≤ M n)
    (hrec : ∀ n, 2 ^ (1729 ^ 12) ≤ n →
      M n ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
        M (3 * rootSize 1729 n * precision n) + A * n * Real.log n)
    (hbase : ∃ B, 0 ≤ B ∧ ∀ n, 2 ≤ n → n < 2 ^ (1729 ^ 12) → M n ≤ B * n * Real.log n) :
    ∃ D, ∀ n, 2 ≤ n → M n ≤ D * n * Real.log n :=
  main_bound (T := transformSize) (r := rootSize 1729) (p := precision) hA
    (two_le_two_pow_pow (d := 1729) (by norm_num)) hM0 (fun n hn => recurrence_params hn) hrec hbase

end IntegerMultBounds.NLogN
