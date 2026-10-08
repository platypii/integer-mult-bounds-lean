import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Parameter selection of Harvey and van der Hoeven, Section 5.1. For an
`n`-bit input with `n ≥ 2^(d^12)` the chunk size `b = ⌈log₂ n⌉`, precision
`p = 6b`, decay parameter `α = ⌈(12 d² b)^(1/4)⌉`, scale `γ = 2 d α²`,
transform length `T` (a power of two in `[4n/b, 8n/b)`), and root size `r`
(a power of two with `T^(1/d) ≤ r < 2 T^(1/d)`) are defined, and the
inequalities (5.1)–(5.9) and (5.12) are proved: `b ≥ d^12 ≥ 4096`,
`2 ≤ α`, `α² < p`, `γ < b − 13`, `T < n < 2^p`, `T ≥ 2^(2d)`, the
factorisation `T = t₁ ⋯ t_d` into powers of two `2 ≤ t₁ ≤ ⋯ ≤ t_d ≤ r`, and
`S > T/2` when every `s_i/t_i > 1 − 1/(2d)`. Nothing here selects the primes
`s_i`, which needs primes in short intervals, or bounds any cost. -/

namespace IntegerMultBounds.NLogN

/-- Chunk size `b = ⌈log₂ n⌉` (5.1). -/
def chunkSize (n : ℕ) : ℕ := Nat.clog 2 n

/-- Working precision `p = 6b` (5.2). -/
def precision (n : ℕ) : ℕ := 6 * chunkSize n

/-- Decay parameter `α = ⌈(12 d² b)^(1/4)⌉` (5.3). -/
noncomputable def alphaParam (d n : ℕ) : ℕ :=
  ⌈((12 * d ^ 2 * chunkSize n : ℕ) : ℝ) ^ (1 / 4 : ℝ)⌉₊

/-- Scale exponent `γ = 2 d α²` (5.5). -/
noncomputable def gammaParam (d n : ℕ) : ℕ := 2 * d * alphaParam d n ^ 2

/-- `⌈4n / b⌉`. -/
def chunkCount4 (n : ℕ) : ℕ := (4 * n + chunkSize n - 1) / chunkSize n

/-- `log₂ T` where `T` is the least power of two with `T ≥ 4n/b`. -/
def transformExp (n : ℕ) : ℕ := Nat.clog 2 (chunkCount4 n)

/-- Transform length `T` (5.6). -/
def transformSize (n : ℕ) : ℕ := 2 ^ transformExp n

/-- `⌈log₂ T / d⌉`. -/
def rootExp (d n : ℕ) : ℕ := (transformExp n + d - 1) / d

/-- Root size `r = 2^⌈log₂ T / d⌉` (5.7). -/
def rootSize (d n : ℕ) : ℕ := 2 ^ rootExp d n

/-- `d₀ = log₂ (r^d / T)`, the number of factors equal to `r/2`. -/
def dimShift (d n : ℕ) : ℕ := d * rootExp d n - transformExp n

/-! ### Chunk size -/

theorem chunkSize_ge {d n : ℕ} (hn : 2 ^ (d ^ 12) ≤ n) : d ^ 12 ≤ chunkSize n := by
  unfold chunkSize
  rcases Nat.eq_zero_or_pos (d ^ 12) with h | h
  · simp [h]
  · have : d ^ 12 - 1 < Nat.clog 2 n := by
      rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
      calc 2 ^ (d ^ 12 - 1) < 2 ^ (d ^ 12) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ ≤ n := hn
    omega

theorem pow_twelve_ge {d : ℕ} (hd : 2 ≤ d) : 4096 ≤ d ^ 12 :=
  calc 4096 = 2 ^ 12 := by norm_num
    _ ≤ d ^ 12 := Nat.pow_le_pow_left hd 12

theorem chunkSize_ge_4096 {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    4096 ≤ chunkSize n :=
  (pow_twelve_ge hd).trans (chunkSize_ge hn)

theorem precision_ge {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    24576 ≤ precision n := by
  unfold precision
  have := chunkSize_ge_4096 hd hn
  omega

theorem n_le_two_pow_chunk (n : ℕ) : n ≤ 2 ^ chunkSize n :=
  Nat.le_pow_clog (by norm_num) n

theorem two_pow_chunk_lt {n : ℕ} (hn : 2 ≤ n) : 2 ^ chunkSize n < 2 * n := by
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
  have h2 := Nat.clog_pos (b := 2) (by norm_num) (n := n) (by omega)
  unfold chunkSize
  calc 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
        rw [← pow_succ']; exact congrArg _ (Nat.succ_pred_eq_of_pos h2).symm
    _ < 2 * n := by omega

theorem chunkSize_le (n : ℕ) : chunkSize n ≤ n :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem chunkSize_le_log_succ (n : ℕ) : chunkSize n ≤ Nat.log 2 n + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) n).le

/-! ### The decay parameter -/

theorem alphaParam_pow_ge (d n : ℕ) : 12 * d ^ 2 * chunkSize n ≤ alphaParam d n ^ 4 := by
  set x : ℝ := ((12 * d ^ 2 * chunkSize n : ℕ) : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x ^ (1 / 4 : ℝ) ≤ (alphaParam d n : ℝ) := Nat.le_ceil _
  have h2 : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    have : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [this, Real.rpow_inv_natCast_pow hx0 (by norm_num)]
  have h3 : x ≤ (alphaParam d n : ℝ) ^ 4 := by
    rw [← h2]; exact pow_le_pow_left₀ (by positivity) h1 4
  rw [hx] at h3
  exact_mod_cast h3

theorem alphaParam_pos {d n : ℕ} (h : 0 < 12 * d ^ 2 * chunkSize n) : 1 ≤ alphaParam d n := by
  have := alphaParam_pow_ge d n
  by_contra hlt
  have h0 : alphaParam d n = 0 := by omega
  have : alphaParam d n ^ 4 = 0 := by rw [h0]; norm_num
  omega

theorem alphaParam_pred_pow_lt {d n : ℕ} (h : 0 < 12 * d ^ 2 * chunkSize n) :
    (alphaParam d n - 1) ^ 4 < 12 * d ^ 2 * chunkSize n := by
  set x : ℝ := ((12 * d ^ 2 * chunkSize n : ℕ) : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : (alphaParam d n : ℝ) < x ^ (1 / 4 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    have : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [this, Real.rpow_inv_natCast_pow hx0 (by norm_num)]
  have hα := alphaParam_pos h
  have h3 : ((alphaParam d n - 1 : ℕ) : ℝ) < x ^ (1 / 4 : ℝ) := by
    rw [Nat.cast_sub hα]; push_cast; linarith
  have h4 : ((alphaParam d n - 1 : ℕ) : ℝ) ^ 4 < x := by
    rw [← h2]; exact pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
  rw [hx] at h4
  exact_mod_cast h4

theorem alphaParam_ge_two {d n : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ chunkSize n) :
    2 ≤ alphaParam d n := by
  have h := alphaParam_pow_ge d n
  have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  by_contra hlt
  have : alphaParam d n ^ 4 ≤ 1 ^ 4 := Nat.pow_le_pow_left (by omega) 4
  nlinarith

theorem alphaParam_ge_22 {d n : ℕ} (hd : 2 ≤ d) (hb : 4096 ≤ chunkSize n) :
    22 ≤ alphaParam d n := by
  have h := alphaParam_pow_ge d n
  have hd2 : 4 ≤ d ^ 2 := by nlinarith
  have hX : 196608 ≤ 12 * d ^ 2 * chunkSize n := by nlinarith
  by_contra hlt
  have : alphaParam d n ^ 4 ≤ 21 ^ 4 := Nat.pow_le_pow_left (by omega) 4
  omega

/-- A crude form of (5.4): `α² < p`. -/
theorem alphaParam_sq_lt_precision {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    alphaParam d n ^ 2 < precision n := by
  have hb := chunkSize_ge_4096 hd hn
  have hd12 := chunkSize_ge hn
  have hα := alphaParam_ge_two (d := d) (n := n) (by omega) (by omega)
  have hlt := alphaParam_pred_pow_lt (d := d) (n := n) (by positivity)
  unfold precision
  set a := alphaParam d n with ha
  set b := chunkSize n with hb'
  -- `α ≤ 2 (α - 1)`, so `α⁴ ≤ 16 (α-1)⁴ < 192 d² b`, while `b ≥ d^12 ≥ 1024 d²`.
  have h1 : a ≤ 2 * (a - 1) := by omega
  have h2 : a ^ 4 ≤ (2 * (a - 1)) ^ 4 := Nat.pow_le_pow_left h1 4
  have h3 : (2 * (a - 1)) ^ 4 = 16 * (a - 1) ^ 4 := by ring
  have h4 : d ^ 12 = d ^ 2 * d ^ 10 := by ring
  have h5 : 1024 ≤ d ^ 10 := by
    calc 1024 = 2 ^ 10 := by norm_num
      _ ≤ d ^ 10 := Nat.pow_le_pow_left hd 10
  have h6 : 1024 * d ^ 2 ≤ b := by
    calc 1024 * d ^ 2 ≤ d ^ 10 * d ^ 2 := Nat.mul_le_mul_right _ h5
      _ = d ^ 12 := by ring
      _ ≤ b := hd12
  by_contra hcon
  push Not at hcon
  -- `a² ≥ 6b` gives `a⁴ ≥ 36 b²`.
  have h7 : (6 * b) ^ 2 ≤ (a ^ 2) ^ 2 := Nat.pow_le_pow_left hcon 2
  have h8 : 36 * b ^ 2 < 192 * d ^ 2 * b := by nlinarith
  have hbpos : 0 < b := by omega
  have h9 : 36 * b < 192 * d ^ 2 := by nlinarith
  nlinarith

theorem alphaParam_le {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    alphaParam d n ≤ 2 * chunkSize n := by
  have h := alphaParam_sq_lt_precision hd hn
  unfold precision at h
  have hb := chunkSize_ge_4096 hd hn
  nlinarith

/-! ### The scale exponent -/

/-- `d⁴ ≤ b/194` once `d^12 ≤ b` and `b ≥ 4096`. -/
theorem pow_four_mul_le {d b : ℕ} (hd : d ^ 12 ≤ b) (hb : 4096 ≤ b) : 194 * d ^ 4 ≤ b := by
  set D := d ^ 4 with hD
  have hD3 : D ^ 3 ≤ b := by rw [hD, ← pow_mul]; exact hd
  by_contra hlt
  push Not at hlt
  have h1 : (b + 1) ^ 3 ≤ (194 * D) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (194 * D) ^ 3 = 194 ^ 3 * D ^ 3 := by ring
  have h3 : (b + 1) ^ 3 ≤ 194 ^ 3 * b := by
    calc (b + 1) ^ 3 ≤ (194 * D) ^ 3 := h1
      _ = 194 ^ 3 * D ^ 3 := h2
      _ ≤ 194 ^ 3 * b := Nat.mul_le_mul_left _ hD3
  have h4 : b ^ 3 ≤ (b + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h5 : b ^ 2 * b ≤ 194 ^ 3 * b := by
    calc b ^ 2 * b = b ^ 3 := by ring
      _ ≤ (b + 1) ^ 3 := h4
      _ ≤ 194 ^ 3 * b := h3
  have h6 : b ^ 2 ≤ 194 ^ 3 := Nat.le_of_mul_le_mul_right h5 (by omega)
  have h7 : 4096 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
  norm_num at h6 h7
  omega

/-- (5.5): `γ < b − 13`; in fact `γ + 14 < b`. -/
theorem gammaParam_add_lt {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    gammaParam d n + 14 < chunkSize n := by
  have hb := chunkSize_ge_4096 hd hn
  have hd12 := chunkSize_ge hn
  have h22 := alphaParam_ge_22 hd hb
  have hlt := alphaParam_pred_pow_lt (d := d) (n := n) (by positivity)
  unfold gammaParam
  set a := alphaParam d n with ha
  set b := chunkSize n with hb'
  set m := a - 1 with hm
  have ham : a = m + 1 := by omega
  have hm21 : 21 ≤ m := by omega
  -- `(m+1)² ≤ 2 m²` for `m ≥ 3`.
  have h1 : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
  set γ := 2 * d * a ^ 2 with hγ
  have h2 : γ ≤ 4 * d * m ^ 2 := by rw [hγ, ham]; nlinarith
  have h3 : γ ^ 2 ≤ 16 * d ^ 2 * m ^ 4 := by
    calc γ ^ 2 ≤ (4 * d * m ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 16 * d ^ 2 * m ^ 4 := by ring
  have hdpos : 0 < d ^ 2 := by positivity
  have h4 : 16 * d ^ 2 * m ^ 4 < 16 * d ^ 2 * (12 * d ^ 2 * b) :=
    Nat.mul_lt_mul_of_pos_left hlt (by positivity)
  have h5 : γ ^ 2 < 192 * d ^ 4 * b := by
    calc γ ^ 2 ≤ 16 * d ^ 2 * m ^ 4 := h3
      _ < 16 * d ^ 2 * (12 * d ^ 2 * b) := h4
      _ = 192 * d ^ 4 * b := by ring
  have hD := pow_four_mul_le hd12 hb
  set D := d ^ 4 with hD'
  -- `γ² < 192 D b ≤ (b − 14)²`.
  obtain ⟨c, hc⟩ : ∃ c, b = c + 14 := ⟨b - 14, by omega⟩
  have hc' : 4082 ≤ c := by omega
  have h6 : 194 * (192 * D * b) ≤ 192 * b * b := by
    calc 194 * (192 * D * b) = 192 * b * (194 * D) := by ring
      _ ≤ 192 * b * b := Nat.mul_le_mul_left _ hD
  have h7 : 192 * b * b ≤ 194 * c ^ 2 := by
    rw [hc]; nlinarith
  have h8 : 194 * γ ^ 2 < 194 * c ^ 2 := by omega
  have h9 : γ ^ 2 < c ^ 2 := by omega
  have h10 : γ < c := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h9
  omega

theorem gammaParam_lt {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    gammaParam d n < chunkSize n - 13 := by
  have := gammaParam_add_lt hd hn
  omega

theorem gammaParam_lt_precision {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    gammaParam d n < precision n := by
  have := gammaParam_add_lt hd hn
  unfold precision
  omega

/-! ### Transform length -/

theorem chunkCount4_mul_ge {n : ℕ} (hb : 1 ≤ chunkSize n) :
    4 * n ≤ chunkCount4 n * chunkSize n := by
  unfold chunkCount4
  have := Nat.lt_div_mul_add (a := 4 * n + chunkSize n - 1) hb
  omega

theorem chunkCount4_pred_mul_lt {n : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ chunkSize n) :
    (chunkCount4 n - 1) * chunkSize n < 4 * n := by
  unfold chunkCount4
  have h := Nat.div_mul_le_self (4 * n + chunkSize n - 1) (chunkSize n)
  rw [Nat.sub_one_mul]
  omega

theorem chunkCount4_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ chunkCount4 n := by
  have hb : 1 ≤ chunkSize n := Nat.clog_pos (by norm_num) (by omega)
  have h1 := chunkCount4_mul_ge (n := n) hb
  have h2 := chunkSize_le n
  by_contra hlt
  have : chunkCount4 n ≤ 1 := by omega
  have : chunkCount4 n * chunkSize n ≤ 1 * chunkSize n := Nat.mul_le_mul_right _ this
  omega

/-- (5.6): `4n ≤ T b < 8n`. -/
theorem transformSize_bounds {n : ℕ} (hn : 2 ≤ n) :
    4 * n ≤ transformSize n * chunkSize n ∧ transformSize n * chunkSize n < 8 * n := by
  have hb : 1 ≤ chunkSize n := Nat.clog_pos (by norm_num) (by omega)
  have hq := chunkCount4_ge_two hn
  constructor
  · calc 4 * n ≤ chunkCount4 n * chunkSize n := chunkCount4_mul_ge hb
      _ ≤ transformSize n * chunkSize n :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) _)
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := chunkCount4 n) (by omega)
    have h2 := Nat.clog_pos (b := 2) (by norm_num) (n := chunkCount4 n) (by omega)
    have h3 : transformSize n = 2 * 2 ^ (Nat.clog 2 (chunkCount4 n)).pred := by
      unfold transformSize transformExp
      rw [← pow_succ']; exact congrArg _ (Nat.succ_pred_eq_of_pos h2).symm
    have h4 : 2 ^ (Nat.clog 2 (chunkCount4 n)).pred ≤ chunkCount4 n - 1 := by omega
    have h5 := chunkCount4_pred_mul_lt (n := n) (by omega) hb
    calc transformSize n * chunkSize n
        = 2 * (2 ^ (Nat.clog 2 (chunkCount4 n)).pred * chunkSize n) := by rw [h3]; ring
      _ ≤ 2 * ((chunkCount4 n - 1) * chunkSize n) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
      _ < 2 * (4 * n) := by omega
      _ = 8 * n := by ring

/-- (5.9): `T < n`. -/
theorem transformSize_lt {n : ℕ} (hn : 2 ≤ n) (hb : 8 ≤ chunkSize n) :
    transformSize n < n := by
  have h := (transformSize_bounds hn).2
  have : transformSize n * 8 ≤ transformSize n * chunkSize n := Nat.mul_le_mul_left _ hb
  omega

theorem transformSize_lt_two_pow_precision {n : ℕ} (hn : 2 ≤ n) (hb : 8 ≤ chunkSize n) :
    transformSize n < 2 ^ precision n := by
  calc transformSize n < n := transformSize_lt hn hb
    _ ≤ 2 ^ chunkSize n := n_le_two_pow_chunk n
    _ ≤ 2 ^ precision n := Nat.pow_le_pow_right (by norm_num) (by unfold precision; omega)

theorem log_transformSize (n : ℕ) : Nat.log 2 (transformSize n) = transformExp n :=
  Nat.log_pow (by norm_num) _

/-! ### Root size -/

theorem rootExp_mul_ge {d n : ℕ} (hd : 1 ≤ d) : transformExp n ≤ rootExp d n * d := by
  unfold rootExp
  have := Nat.lt_div_mul_add (a := transformExp n + d - 1) hd
  omega

theorem rootExp_mul_lt {d n : ℕ} (hd : 1 ≤ d) : rootExp d n * d < transformExp n + d := by
  unfold rootExp
  have := Nat.div_mul_le_self (transformExp n + d - 1) d
  omega

/-- (5.7): `T ≤ r^d < 2^d T`. -/
theorem rootSize_pow_bounds {d n : ℕ} (hd : 1 ≤ d) :
    transformSize n ≤ rootSize d n ^ d ∧ rootSize d n ^ d < 2 ^ d * transformSize n := by
  unfold rootSize transformSize
  rw [← pow_mul, ← pow_add]
  exact ⟨Nat.pow_le_pow_right (by norm_num) (rootExp_mul_ge hd),
    Nat.pow_lt_pow_right (by norm_num) (by have := rootExp_mul_lt (n := n) hd; omega)⟩

theorem dimShift_lt {d n : ℕ} (hd : 1 ≤ d) : dimShift d n < d := by
  unfold dimShift
  have := rootExp_mul_lt (n := n) hd
  rw [mul_comm]
  omega

/-! ### Lower bound on the transform length -/

theorem two_mul_add_two_lt_two_pow {k : ℕ} (hk : 4 ≤ k) : 2 * k + 2 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem succ_lt_two_pow_half {L : ℕ} (hL : 8 ≤ L) : L + 1 < 2 ^ (L / 2) := by
  have := two_mul_add_two_lt_two_pow (k := L / 2) (by omega)
  omega

/-- (5.8): `T ≥ 2^(2d)`; in fact `T > 2^(2d+2)`. -/
theorem transformSize_ge {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    2 ^ (2 * d) ≤ transformSize n := by
  set L := Nat.log 2 n with hL
  have hd12 := pow_twelve_ge hd
  have hLd : d ^ 12 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hn2 : 2 ≤ n := by
    calc 2 ≤ 2 ^ (d ^ 12) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (d ^ 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := hn
  have hnL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hb := chunkSize_le_log_succ n
  have hT := (transformSize_bounds hn2).1
  have hL8 : 8 ≤ L := by omega
  have hhalf := succ_lt_two_pow_half hL8
  set T := transformSize n with hT'
  have hTpos : 0 < T := by unfold transformSize at hT'; rw [hT']; positivity
  -- `4 · 2^L ≤ 4n ≤ T b ≤ T (L+1) < T 2^(L/2)`.
  have h1 : 4 * 2 ^ L < T * 2 ^ (L / 2) := by
    calc 4 * 2 ^ L ≤ 4 * n := by omega
      _ ≤ T * chunkSize n := hT
      _ ≤ T * (L + 1) := Nat.mul_le_mul_left _ hb
      _ < T * 2 ^ (L / 2) := Nat.mul_lt_mul_of_pos_left hhalf hTpos
  have h2 : 2 ^ (L / 2) * 2 ^ (L / 2) ≤ 2 ^ L := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (4 * 2 ^ (L / 2)) * 2 ^ (L / 2) < T * 2 ^ (L / 2) := by
    calc (4 * 2 ^ (L / 2)) * 2 ^ (L / 2) = 4 * (2 ^ (L / 2) * 2 ^ (L / 2)) := by ring
      _ ≤ 4 * 2 ^ L := Nat.mul_le_mul_left _ h2
      _ < T * 2 ^ (L / 2) := h1
  have h4 : 4 * 2 ^ (L / 2) < T := Nat.lt_of_mul_lt_mul_right h3
  have h5 : 2 ^ (2 * d) ≤ 2 ^ (L / 2) := by
    apply Nat.pow_le_pow_right (by norm_num)
    have : 4 * d ≤ d ^ 12 := by
      calc 4 * d ≤ d ^ 11 * d := Nat.mul_le_mul_right _
            (calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
              _ ≤ d ^ 11 := Nat.pow_le_pow_left hd 11)
        _ = d ^ 12 := by ring
    omega
  omega

theorem rootExp_ge_two {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) : 2 ≤ rootExp d n := by
  have hT := transformSize_ge hd hn
  have he : 2 * d ≤ transformExp n := by
    unfold transformSize at hT
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hT
  unfold rootExp
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

/-! ### The factorisation `T = t₁ ⋯ t_d` -/

theorem filter_lt_range {d₀ d : ℕ} (h : d₀ ≤ d) :
    (Finset.range d).filter (fun i => i < d₀) = Finset.range d₀ := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem filter_not_lt_range {d₀ d : ℕ} (_h : d₀ ≤ d) :
    (Finset.range d).filter (fun i => ¬ i < d₀) = Finset.Ico d₀ d := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- The factors `t_i` of (5.8): `r/2` for `i < d₀` and `r` otherwise. -/
def factorAt (d n : ℕ) (i : ℕ) : ℕ :=
  if i < dimShift d n then 2 ^ (rootExp d n - 1) else 2 ^ rootExp d n

theorem factorAt_prod {d n : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ rootExp d n) :
    ∏ i ∈ Finset.range d, factorAt d n i = transformSize n := by
  unfold factorAt
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    filter_lt_range (dimShift_lt hd).le, filter_not_lt_range (dimShift_lt hd).le,
    Finset.card_range, Nat.card_Ico, ← pow_mul, ← pow_mul, ← pow_add]
  unfold transformSize
  congr 1
  have h1 := rootExp_mul_ge (n := n) hd
  have h2 := dimShift_lt (n := n) hd
  unfold dimShift at h2 ⊢
  set k := rootExp d n
  set e := transformExp n
  set d₀ := d * k - e with hd₀
  have h3 : d₀ ≤ d * k := Nat.sub_le _ _
  have h4 : (k - 1) * d₀ = k * d₀ - d₀ := Nat.sub_one_mul _ _
  have h5 : k * (d - d₀) = k * d - k * d₀ := Nat.mul_sub _ _ _
  have h6 : d₀ ≤ k * d₀ := Nat.le_mul_of_pos_left _ hk
  have h7 : k * d₀ ≤ k * d := Nat.mul_le_mul_left _ h2.le
  have h8 : k * d = d * k := mul_comm _ _
  rw [h4, h5]
  omega

/-- The factorisation of `T` into `d` powers of two between `2` and `r`, nondecreasing. -/
theorem exists_factorisation {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ^ (d ^ 12) ≤ n) :
    ∃ t : Fin d → ℕ, (∀ i, ∃ e, t i = 2 ^ e) ∧ (∀ i, 2 ≤ t i) ∧ Monotone t ∧
      ∏ i, t i = transformSize n ∧ ∀ i, t i ≤ rootSize d n := by
  have hk := rootExp_ge_two hd hn
  refine ⟨fun i => factorAt d n i.val, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [factorAt]
    split_ifs <;> exact ⟨_, rfl⟩
  · intro i
    simp only [factorAt]
    split_ifs
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (rootExp d n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ rootExp d n := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro i j hij
    simp only [factorAt]
    have hij' : i.val ≤ j.val := hij
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · omega
    · exact le_rfl
  · rw [Fin.prod_univ_eq_prod_range (fun i => factorAt d n i) d]
    exact factorAt_prod (by omega) (by omega)
  · intro i
    simp only [factorAt, rootSize]
    split_ifs
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact le_rfl

/-! ### (5.12): `S > T/2` -/

/-- If every ratio `s_i / t_i` exceeds `1 − 1/(2d)`, then `∏ s_i > (1/2) ∏ t_i`. -/
theorem two_mul_prod_gt {d : ℕ} (hd : 1 ≤ d) (s t : Fin d → ℕ) (ht : ∀ i, 0 < t i)
    (hst : ∀ i, (4 * d - 2) * t i < 4 * d * s i) : ∏ i, t i < 2 * ∏ i, s i := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  set q : ℝ := 1 - 1 / (2 * ((d' + 1 : ℕ) : ℝ)) with hq
  have hd' : (1 : ℝ) ≤ ((d' + 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hqpos : 0 < q := by
    rw [hq, sub_pos, div_lt_one (by positivity)]; linarith
  -- pointwise `q < s i / t i`
  have hpt : ∀ i, q < (s i : ℝ) / t i := by
    intro i
    have h := hst i
    have ht' : (0 : ℝ) < t i := by exact_mod_cast ht i
    rw [lt_div_iff₀ ht']
    have h' : ((4 * (d' + 1) - 2 : ℕ) : ℝ) * t i < 4 * ((d' + 1 : ℕ) : ℝ) * s i := by
      exact_mod_cast h
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h' ⊢
    have h4 : (0 : ℝ) < 4 * ((d' : ℝ) + 1) := by positivity
    have hq' : q * (t i : ℝ) * (4 * ((d' : ℝ) + 1)) = (4 * ((d' : ℝ) + 1) - 2) * t i := by
      rw [hq]; push_cast; field_simp; ring
    by_contra hcon
    push Not at hcon
    have : 4 * ((d' : ℝ) + 1) * s i ≤ (4 * ((d' : ℝ) + 1) - 2) * t i := by
      rw [← hq']
      calc 4 * ((d' : ℝ) + 1) * s i = (s i : ℝ) * (4 * ((d' : ℝ) + 1)) := by ring
        _ ≤ (q * t i) * (4 * ((d' : ℝ) + 1)) := by gcongr
        _ = q * (t i : ℝ) * (4 * ((d' : ℝ) + 1)) := by ring
    linarith
  -- product over the tail is at least `q^d'`, and the head factor is strictly larger than `q`.
  have htail : q ^ d' ≤ ∏ i : Fin d', ((s i.succ : ℝ) / t i.succ) := by
    calc q ^ d' = ∏ _i : Fin d', q := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin d', ((s i.succ : ℝ) / t i.succ) :=
        Finset.prod_le_prod₀ (fun i _ => hqpos.le) (fun i _ => (hpt i.succ).le)
  have hprod : q ^ (d' + 1) < ∏ i : Fin (d' + 1), ((s i : ℝ) / t i) := by
    rw [Fin.prod_univ_succ, pow_succ']
    have hq0 : 0 < q ^ d' := pow_pos hqpos _
    calc q * q ^ d' < ((s 0 : ℝ) / t 0) * q ^ d' := by
          exact mul_lt_mul_of_pos_right (hpt 0) hq0
      _ ≤ ((s 0 : ℝ) / t 0) * ∏ i : Fin d', ((s i.succ : ℝ) / t i.succ) := by
          apply mul_le_mul_of_nonneg_left htail
          have := ht 0
          positivity
  -- Bernoulli: `q^(d'+1) ≥ 1/2`.
  have hbern : (1 : ℝ) / 2 ≤ q ^ (d' + 1) := by
    have hD : (0 : ℝ) < ((d' + 1 : ℕ) : ℝ) := by positivity
    have h := one_add_mul_le_pow (a := -(1 / (2 * ((d' + 1 : ℕ) : ℝ))))
      (by
        have : (1 : ℝ) / (2 * ((d' + 1 : ℕ) : ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        linarith) (d' + 1)
    have h2 : (1 : ℝ) + ((d' + 1 : ℕ) : ℝ) * -(1 / (2 * ((d' + 1 : ℕ) : ℝ))) = 1 / 2 := by
      field_simp; ring
    rw [h2] at h
    rw [hq]
    convert h using 2
  rw [Finset.prod_div_distrib] at hprod
  have htpos : (0 : ℝ) < ∏ i : Fin (d' + 1), (t i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast ht i)
  rw [lt_div_iff₀ htpos] at hprod
  have : (∏ i : Fin (d' + 1), (t i : ℝ)) < 2 * ∏ i : Fin (d' + 1), (s i : ℝ) := by nlinarith
  exact_mod_cast this

end IntegerMultBounds.NLogN
