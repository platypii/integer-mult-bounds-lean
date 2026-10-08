import IntegerMultBounds.NLogN.Approx
import IntegerMultBounds.NLogN.Recurrence
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Lemma 2.13 of Harvey–van der Hoeven, the evaluation of `e^(−z)` to `p`
bits, split into the parts the cost model needs. Proved: the truncated Taylor
series of `exp` on `[−1, 1]` is within `2/K!` of the value; a term count
`termCount p = 8 (⌊p / log₂ p⌋ + 1) + 8`, sublinear in `p`, has
`(termCount p)! ≥ 2^(p+1)`; the reduction `e^(−z) = (e^(−1))^⌊z⌋ e^(−(z − ⌊z⌋))`
with both factors by truncated series has error at most `3 (⌊z⌋ + 1) · 2/K!`
whenever `⌊z⌋ · 2/K! ≤ 1`; and the operation count of binary splitting, the
cost recursion `B(j+1) = 2 B(j) + 4 M(2^(j+1) L)` on exact rationals of
`2^j L` bits at depth `j`, is at most `2^J L + 4 J M(2^J L)` for a
superadditive multiplication cost, so evaluating `e^(−z)` with the sublinear
term count costs `O(M(80 p) log p)` word operations, the paper's `O(p^(1+δ))`
for quasilinear `M`. Not here: the exact-rational correctness of the binary
splitting product tree, and the computation of the `p`-bit approximation of
`π · (rational)` that precedes the exponential. -/

namespace IntegerMultBounds.NLogN

open Finset

/-! ### Truncated Taylor series -/

/-- The partial sum of the exponential series. -/
noncomputable def taylorSum (K : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range K, x ^ i / (i.factorial : ℝ)

theorem exp_taylor_err (x : ℝ) (hx : |x| ≤ 1) (K : ℕ) (hK : 0 < K) :
    |Real.exp x - taylorSum K x| ≤ 2 / (K.factorial : ℝ) := by
  have h := Real.exp_bound hx hK
  have hfac : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpow : |x| ^ K ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hfrac : ((K.succ : ℕ) : ℝ) / ((K.factorial : ℝ) * K) ≤ 2 / (K.factorial : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hfac]
    push_cast
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    calc ((K : ℝ) + 1) * K.factorial ≤ (2 * K) * K.factorial :=
          mul_le_mul_of_nonneg_right (by linarith) hfac.le
      _ = 2 * ((K.factorial : ℝ) * K) := by ring
  calc |Real.exp x - taylorSum K x|
      ≤ |x| ^ K * ((K.succ : ℕ) / ((K.factorial : ℝ) * K)) := h
    _ ≤ 1 * (2 / (K.factorial : ℝ)) := by
        apply mul_le_mul hpow hfrac (by positivity) zero_le_one
    _ = 2 / (K.factorial : ℝ) := one_mul _

/-- `(⌊K/2⌋ + 1)^⌊K/2⌋ ≤ K!`. -/
theorem half_pow_le_factorial (K : ℕ) : (K / 2 + 1) ^ (K / 2) ≤ K.factorial := by
  have h1 : (K / 2).factorial * (K / 2 + 1) ^ (K - K / 2) ≤ (K / 2 + (K - K / 2)).factorial :=
    Nat.factorial_mul_pow_le_factorial
  have h2 : K / 2 + (K - K / 2) = K := by omega
  rw [h2] at h1
  have h3 : (K / 2 + 1) ^ (K / 2) ≤ (K / 2 + 1) ^ (K - K / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 1 ≤ (K / 2).factorial := Nat.factorial_pos _
  calc (K / 2 + 1) ^ (K / 2) ≤ (K / 2 + 1) ^ (K - K / 2) := h3
    _ ≤ (K / 2).factorial * (K / 2 + 1) ^ (K - K / 2) := Nat.le_mul_of_pos_left _ h4
    _ ≤ K.factorial := h1

/-- The sublinear number of Taylor terms used at precision `p`. -/
def termCount (p : ℕ) : ℕ := 8 * (p / Nat.log 2 p + 1) + 8

theorem two_mul_succ_le_two_pow (h : ℕ) : 2 * h + 1 ≤ 2 ^ (h + 1) := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    have : 2 ≤ 2 ^ (h + 1) := Nat.one_lt_two_pow (by omega)
    rw [pow_succ]
    omega

theorem log_ge_four (p : ℕ) (hp : 16 ≤ p) : 4 ≤ Nat.log 2 p :=
  Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hp)

theorem termCount_le (p : ℕ) (hp : 16 ≤ p) : termCount p ≤ 2 * p + 16 := by
  have hL := log_ge_four p hp
  have : p / Nat.log 2 p ≤ p / 4 := Nat.div_le_div_left hL (by norm_num)
  unfold termCount
  omega

/-- The factorial of the term count beats `2^(p+1)`: `K! ≥ 2^(p+1)`. -/
theorem two_pow_le_termCount_factorial (p : ℕ) (hp : 16 ≤ p) :
    2 ^ (p + 1) ≤ (termCount p).factorial := by
  set L := Nat.log 2 p with hLdef
  have hL : 4 ≤ L := log_ge_four p hp
  have hLpos : 0 < L := by omega
  set q := p / L + 1 with hq
  set h := L / 2 with hh
  -- `q L ≥ p + 1`
  have hdm : (p / L) * L + p % L = p := by rw [Nat.mul_comm]; exact Nat.div_add_mod p L
  have hmod := Nat.mod_lt p hLpos
  have hqL : p + 1 ≤ q * L := by
    have : q * L = (p / L) * L + L := by rw [hq]; ring
    rw [this]; omega
  -- `2 h + 1 ≥ L`
  have h2h : L ≤ 2 * h + 1 := by omega
  -- `2^L ≤ p < 2^(L+1)`
  have hpow : 2 ^ L ≤ p := Nat.pow_log_le_self 2 (by omega)
  -- `2^h ≤ 2 (p / L) + 2`
  have hLle : L ≤ 2 ^ (h + 1) := le_trans h2h (two_mul_succ_le_two_pow h)
  have h2pow : 2 ^ h * L ≤ 2 * p := by
    calc 2 ^ h * L ≤ 2 ^ h * 2 ^ (h + 1) := Nat.mul_le_mul_left _ hLle
      _ = 2 ^ (2 * h + 1) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ L := by ring
      _ ≤ 2 * p := by omega
  have hp2 : 2 * p ≤ (2 * (p / L) + 2) * L := by
    have : 2 * p = 2 * ((p / L) * L) + 2 * (p % L) := by omega
    rw [this]; nlinarith
  have h2h' : 2 ^ h ≤ 2 * (p / L) + 2 :=
    Nat.le_of_mul_le_mul_right (le_trans h2pow hp2) hLpos
  have hbase : 2 ^ h ≤ 4 * q + 5 := by omega
  -- `q ≤ p/4 + 1`
  have hq4 : p / L ≤ p / 4 := Nat.div_le_div_left hL (by norm_num)
  have hq4' : 4 * q ≤ p + 4 := by
    have : 4 * (p / 4) ≤ p := Nat.mul_div_le p 4
    omega
  -- `h (4q + 4) ≥ p + 1`
  have hexp : p + 1 ≤ h * (4 * q + 4) := by
    have h2 : 2 * (p + 1) ≤ 2 * h * (4 * q + 4) := by
      have e1 : (L - 1) * (4 * q + 4) ≤ 2 * h * (4 * q + 4) :=
        Nat.mul_le_mul_right _ (by omega)
      have e2 : 2 * (p + 1) ≤ (L - 1) * (4 * q + 4) := by
        have hL1 : L - 1 + 1 = L := by omega
        have : (L - 1) * (4 * q + 4) + (4 * q + 4) = L * (4 * q + 4) := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, hL1]
        nlinarith
      exact le_trans e2 e1
    nlinarith
  have hK2 : termCount p / 2 = 4 * q + 4 := by
    simp only [termCount, ← hLdef, hq]; omega
  calc 2 ^ (p + 1) ≤ 2 ^ (h * (4 * q + 4)) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = (2 ^ h) ^ (4 * q + 4) := by rw [pow_mul]
    _ ≤ (4 * q + 5) ^ (4 * q + 4) := Nat.pow_le_pow_left hbase _
    _ = (termCount p / 2 + 1) ^ (termCount p / 2) := by rw [hK2]
    _ ≤ (termCount p).factorial := half_pow_le_factorial _

/-- With the sublinear term count the truncation error is below `2^(−p)`. -/
theorem exp_taylor_err_termCount (x : ℝ) (hx : |x| ≤ 1) (p : ℕ) (hp : 16 ≤ p) :
    |Real.exp x - taylorSum (termCount p) x| ≤ 1 / 2 ^ p := by
  have hK : 0 < termCount p := by unfold termCount; omega
  have h := exp_taylor_err x hx (termCount p) hK
  have hfac : ((2 : ℕ) ^ (p + 1) : ℝ) ≤ (termCount p).factorial := by
    exact_mod_cast two_pow_le_termCount_factorial p hp
  have hpos : (0 : ℝ) < 2 ^ (p + 1) := by positivity
  calc |Real.exp x - taylorSum (termCount p) x| ≤ 2 / (termCount p).factorial := h
    _ ≤ 2 / ((2 : ℕ) ^ (p + 1) : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hpos hfac
    _ = 1 / 2 ^ p := by push_cast; rw [pow_succ]; field_simp

/-! ### Argument reduction -/

/-- `|a^M − a'^M| ≤ M |a − a'| B^M` for `|a|, |a'| ≤ B`, `1 ≤ B`. -/
theorem abs_pow_sub_pow_le (a a' B : ℝ) (hB : 1 ≤ B) (ha : |a| ≤ B) (ha' : |a'| ≤ B)
    (M : ℕ) : |a ^ M - a' ^ M| ≤ M * |a - a'| * B ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hBM : 0 ≤ B ^ M := by positivity
    have hd : 0 ≤ |a - a'| := abs_nonneg _
    have hsplit : a ^ (M + 1) - a' ^ (M + 1) = a * (a ^ M - a' ^ M) + (a - a') * a' ^ M := by
      ring
    have h1 : |a * (a ^ M - a' ^ M)| ≤ B * (M * |a - a'| * B ^ M) := by
      rw [abs_mul]
      exact mul_le_mul ha ih (abs_nonneg _) (by linarith)
    have h2 : |(a - a') * a' ^ M| ≤ |a - a'| * B ^ M := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ha' M) hd
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    calc |a ^ (M + 1) - a' ^ (M + 1)|
        = |a * (a ^ M - a' ^ M) + (a - a') * a' ^ M| := by rw [hsplit]
      _ ≤ |a * (a ^ M - a' ^ M)| + |(a - a') * a' ^ M| := abs_add_le _ _
      _ ≤ B * (M * |a - a'| * B ^ M) + |a - a'| * B ^ M := add_le_add h1 h2
      _ = (M * B + 1) * |a - a'| * B ^ M := by ring
      _ ≤ ((M + 1) * B) * |a - a'| * B ^ M := by
          apply mul_le_mul_of_nonneg_right _ hBM
          apply mul_le_mul_of_nonneg_right _ hd
          nlinarith
      _ = (M + 1 : ℕ) * |a - a'| * B ^ (M + 1) := by push_cast; ring

/-- The reduced evaluation `(e^(−1))^⌊z⌋ e^(−(z − ⌊z⌋))` with both factors by
truncated series, `ε = 2/K!`. -/
theorem exp_neg_approx_err (z : ℝ) (hz : 0 ≤ z) (K : ℕ) (hK : 0 < K)
    (hMK : (⌊z⌋₊ : ℝ) * (2 / (K.factorial : ℝ)) ≤ 1) :
    |Real.exp (-z) - (taylorSum K (-1)) ^ ⌊z⌋₊ * taylorSum K (-(z - ⌊z⌋₊))| ≤
      3 * (⌊z⌋₊ + 1) * (2 / (K.factorial : ℝ)) := by
  set M := ⌊z⌋₊ with hM
  set ε : ℝ := 2 / (K.factorial : ℝ) with hε
  set y := z - M with hy
  have hε0 : 0 ≤ ε := by positivity
  have hy0 : 0 ≤ y := by rw [hy]; linarith [Nat.floor_le hz]
  have hy1 : y < 1 := by rw [hy]; linarith [Nat.lt_floor_add_one z]
  set a := Real.exp (-1) with ha
  set a' := taylorSum K (-1) with ha'
  set b := Real.exp (-y) with hb
  set b' := taylorSum K (-y) with hb'
  have haa' : |a - a'| ≤ ε := exp_taylor_err (-1) (by simp) K hK
  have hbb' : |b - b'| ≤ ε := exp_taylor_err (-y) (by rw [abs_neg, abs_of_nonneg hy0]; linarith) K hK
  have ha1 : |a| ≤ 1 := by
    rw [ha, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hb1 : |b| ≤ 1 := by
    rw [hb, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have ha'1 : |a'| ≤ 1 + ε := by
    have := abs_sub_abs_le_abs_sub a' a
    rw [abs_sub_comm] at this
    linarith
  -- the exact value factors
  have hexact : Real.exp (-z) = a ^ M * b := by
    have : -z = (M : ℝ) * (-1) + (-y) := by rw [hy]; ring
    rw [this, Real.exp_add, Real.exp_nat_mul]
  -- `(1 + ε)^M ≤ 3`
  have hB : (1 + ε) ^ M ≤ 3 := by
    have h1 : (1 + ε) ^ M ≤ (Real.exp ε) ^ M :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ε]) M
    have h2 : (Real.exp ε) ^ M = Real.exp (M * ε) := by rw [Real.exp_nat_mul]
    have h3 : Real.exp (M * ε) ≤ Real.exp 1 := Real.exp_le_exp.mpr hMK
    have h4 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hBM : 0 ≤ (1 + ε) ^ M := by positivity
  have hpow := abs_pow_sub_pow_le a a' (1 + ε) (by linarith) (by linarith) ha'1 M
  have ha'M : |a' ^ M| ≤ (1 + ε) ^ M := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ha'1 M
  have hsplit : a ^ M * b - a' ^ M * b' = (a ^ M - a' ^ M) * b + a' ^ M * (b - b') := by ring
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  calc |Real.exp (-z) - a' ^ M * b'|
      = |(a ^ M - a' ^ M) * b + a' ^ M * (b - b')| := by rw [hexact, hsplit]
    _ ≤ |(a ^ M - a' ^ M) * b| + |a' ^ M * (b - b')| := abs_add_le _ _
    _ ≤ (M * |a - a'| * (1 + ε) ^ M) * 1 + (1 + ε) ^ M * ε := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hpow hb1 (abs_nonneg _) (by positivity))
          (mul_le_mul ha'M hbb' (abs_nonneg _) hBM)
    _ ≤ (M * ε * 3) * 1 + 3 * ε := by
        have e1 : M * |a - a'| * (1 + ε) ^ M ≤ M * ε * 3 := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left haa' hM0) hB hBM (by positivity)
          linarith
        have e2 : (1 + ε) ^ M * ε ≤ 3 * ε := mul_le_mul_of_nonneg_right hB hε0
        linarith
    _ = 3 * (M + 1) * ε := by ring

/-! ### Operation counts -/

/-- The cost recursion of binary splitting: at depth `j` below the root the
two children are combined with four products of `2^(j+1) L`-bit numbers. -/
def splitOps (Mcost : ℕ → ℕ) (L c : ℕ) : ℕ → ℕ
  | 0 => c
  | j + 1 => 2 * splitOps Mcost L c j + 4 * Mcost (2 ^ (j + 1) * L)

theorem splitOps_le (Mcost : ℕ → ℕ) (hsup : ∀ a b, Mcost a + Mcost b ≤ Mcost (a + b))
    (L c J : ℕ) : splitOps Mcost L c J ≤ 2 ^ J * c + 4 * J * Mcost (2 ^ J * L) := by
  induction J with
  | zero => simp [splitOps]
  | succ J ih =>
    have hdouble : 2 * Mcost (2 ^ J * L) ≤ Mcost (2 ^ (J + 1) * L) := by
      have := hsup (2 ^ J * L) (2 ^ J * L)
      have e : 2 ^ J * L + 2 ^ J * L = 2 ^ (J + 1) * L := by ring
      rw [e] at this; omega
    simp only [splitOps]
    have : 2 ^ (J + 1) * c = 2 * (2 ^ J * c) := by ring
    rw [this]
    nlinarith

/-- Operation count for `e^(−z)` to `p` bits: two binary-splitting series of
`K` terms with `L`-bit leaves, the `⌊z⌋`-th power by repeated squaring, one
final product, and the shifts and roundings. -/
def expOps (Mcost : ℕ → ℕ) (p K L M : ℕ) : ℕ :=
  2 * splitOps Mcost L L (Nat.log 2 K + 1) + (2 * Nat.log 2 (M + 1) + 1) * Mcost p + 4 * p

theorem expOps_le (Mcost : ℕ → ℕ) (hsup : ∀ a b, Mcost a + Mcost b ≤ Mcost (a + b))
    (hmono : Monotone Mcost) (p K L M B : ℕ) (hK : 1 ≤ K) (hKL : 2 * K * L ≤ B) :
    expOps Mcost p K L M ≤
      2 * B + 8 * (Nat.log 2 K + 1) * Mcost B + (2 * Nat.log 2 (M + 1) + 1) * Mcost p + 4 * p := by
  unfold expOps
  set J := Nat.log 2 K + 1 with hJ
  have h2J : 2 ^ J ≤ 2 * K := by
    have := Nat.pow_log_le_self 2 (show K ≠ 0 by omega)
    rw [hJ, pow_succ]; omega
  have hJL : 2 ^ J * L ≤ B := le_trans (Nat.mul_le_mul_right _ h2J) hKL
  have h := splitOps_le Mcost hsup L L J
  have hm : Mcost (2 ^ J * L) ≤ Mcost B := hmono hJL
  have : 2 * splitOps Mcost L L J ≤ 2 * B + 8 * J * Mcost B := by nlinarith
  omega

theorem termCount_mul_log_le (p : ℕ) (hp : 16 ≤ p) :
    termCount p * (Nat.log 2 (termCount p) + 2) ≤ 40 * p := by
  set L := Nat.log 2 p with hL
  have hL4 : 4 ≤ L := log_ge_four p hp
  have hpL : p < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have hT : termCount p ≤ 2 * p + 16 := termCount_le p hp
  have hlog : Nat.log 2 (termCount p) ≤ L + 2 := by
    have h16 : 16 ≤ 2 ^ (L + 2) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : termCount p < 2 ^ (L + 3) := by
      calc termCount p ≤ 2 * p + 16 := hT
        _ < 2 * 2 ^ (L + 1) + 2 ^ (L + 2) := by omega
        _ = 2 ^ (L + 3) := by ring
    have := Nat.log_lt_of_lt_pow' (by omega) this
    omega
  have hq4 : p / L ≤ p / 4 := Nat.div_le_div_left hL4 (by norm_num)
  have h4 : 4 * (p / 4) ≤ p := Nat.mul_div_le p 4
  have hdm : (p / L) * L ≤ p := Nat.div_mul_le_self p L
  have hLp : L ≤ p := Nat.log_le_self 2 p
  have hT' : termCount p = 8 * (p / L) + 16 := by simp only [termCount, ← hL]; ring
  calc termCount p * (Nat.log 2 (termCount p) + 2)
      ≤ (8 * (p / L) + 16) * (L + 4) := Nat.mul_le_mul (le_of_eq hT') (by omega)
    _ = 8 * ((p / L) * L) + 32 * (p / L) + 16 * L + 64 := by ring
    _ ≤ 8 * p + 8 * p + 16 * p + 4 * p := by omega
    _ = 36 * p := by ring
    _ ≤ 40 * p := by omega

/-- Lemma 2.13's cost shape: with the sublinear term count and `⌊z⌋ ≤ 4 p² + 4`,
evaluating `e^(−z)` costs `O(M(80 p) log p)` word operations. -/
theorem expOps_quasi (Mcost : ℕ → ℕ) (hsup : ∀ a b, Mcost a + Mcost b ≤ Mcost (a + b))
    (hmono : Monotone Mcost) (p M : ℕ) (hp : 16 ≤ p) (hM : M ≤ 4 * p ^ 2 + 4) :
    expOps Mcost p (termCount p) (Nat.log 2 (termCount p) + 2) M ≤
      164 * p + 8 * (Nat.log 2 p + 3) * Mcost (80 * p) + (4 * Nat.log 2 p + 9) * Mcost p := by
  set L := Nat.log 2 p with hL
  have hL4 : 4 ≤ L := log_ge_four p hp
  have hK : 1 ≤ termCount p := by unfold termCount; omega
  have hKL : 2 * termCount p * (Nat.log 2 (termCount p) + 2) ≤ 80 * p := by
    have := termCount_mul_log_le p hp
    nlinarith
  have h := expOps_le Mcost hsup hmono p (termCount p) (Nat.log 2 (termCount p) + 2) M (80 * p) hK hKL
  -- `log₂ K + 1 ≤ L + 3`
  have hT : termCount p ≤ 2 * p + 16 := termCount_le p hp
  have hpL : p < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have hlogK : Nat.log 2 (termCount p) ≤ L + 2 := by
    have h16 : 16 ≤ 2 ^ (L + 2) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : termCount p < 2 ^ (L + 3) := by
      calc termCount p ≤ 2 * p + 16 := hT
        _ < 2 * 2 ^ (L + 1) + 2 ^ (L + 2) := by omega
        _ = 2 ^ (L + 3) := by ring
    have := Nat.log_lt_of_lt_pow' (by omega) this
    omega
  -- `log₂ (M + 1) ≤ 2 L + 4`
  have hlogM : Nat.log 2 (M + 1) ≤ 2 * L + 4 := by
    have hp2 : p ^ 2 < 2 ^ (2 * L + 2) := by
      calc p ^ 2 < (2 ^ (L + 1)) ^ 2 := by
            exact Nat.pow_lt_pow_left hpL (by norm_num)
        _ = 2 ^ (2 * L + 2) := by rw [← pow_mul]; congr 1; ring
    have h5 : 5 ≤ 2 ^ (2 * L + 2) := by
      calc 5 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * L + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : M + 1 < 2 ^ (2 * L + 5) := by
      calc M + 1 ≤ 4 * p ^ 2 + 5 := by omega
        _ < 4 * 2 ^ (2 * L + 2) + 2 ^ (2 * L + 2) := by omega
        _ ≤ 2 ^ (2 * L + 5) := by
            have : 2 ^ (2 * L + 5) = 8 * 2 ^ (2 * L + 2) := by ring
            omega
    have := Nat.log_lt_of_lt_pow' (by omega) this
    omega
  have e1 : 8 * (Nat.log 2 (termCount p) + 1) * Mcost (80 * p) ≤
      8 * (L + 3) * Mcost (80 * p) := Nat.mul_le_mul_right _ (by omega)
  have e2 : (2 * Nat.log 2 (M + 1) + 1) * Mcost p ≤ (4 * L + 9) * Mcost p :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end IntegerMultBounds.NLogN
