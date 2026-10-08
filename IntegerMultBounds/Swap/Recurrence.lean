import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! Arithmetic of the chunk-interchange recurrence (§4). A node of width `m^k`
makes `s` recursive calls on streams of volume `V / W`; with `s / W ≤ m^τ` the
normalized cost is `O(m^{kτ})`. The remaining lemmas bound the digit pieces of
a general width, the row padding, the row-range digits, and the radix padding
used to remove the width restrictions. These are statements about numbers, not
about a machine. -/

namespace IntegerMultBounds.Swap.Recurrence

open Finset

/-- A geometric sum with ratio at most `x > 1` is at most `x^(k+1) / (x - 1)`.
No case split on the ratio is needed. -/
theorem geom_sum_le_of_le {a x : ℝ} (ha : 0 ≤ a) (hx : 1 < x) (hax : a ≤ x) (k : ℕ) :
    ∑ j ∈ range (k + 1), a ^ j ≤ x ^ (k + 1) / (x - 1) := by
  have hx1 : 0 < x - 1 := by linarith
  calc
    ∑ j ∈ range (k + 1), a ^ j ≤ ∑ j ∈ range (k + 1), x ^ j := by
      gcongr with j
    _ = (x ^ (k + 1) - 1) / (x - 1) := geom_sum_eq hx.ne' _
    _ ≤ x ^ (k + 1) / (x - 1) := by
      apply div_le_div_of_nonneg_right _ hx1.le
      linarith

/-- The normalized recurrence `F (k+1) ≤ a F k + C` unrolls to a geometric sum. -/
theorem unroll {F : ℕ → ℝ} {a L C : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbase : F 0 ≤ L) (hstep : ∀ k, F (k + 1) ≤ a * F k + C) :
    ∀ k, F k ≤ (L + C) * ∑ j ∈ range (k + 1), a ^ j := by
  intro k
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    rw [geom_sum_succ]
    have hs : 0 ≤ ∑ j ∈ range (k + 1), a ^ j := sum_nonneg (fun j _ => pow_nonneg ha j)
    calc
      F (k + 1) ≤ a * F k + C := hstep k
      _ ≤ a * ((L + C) * ∑ j ∈ range (k + 1), a ^ j) + C := by gcongr
      _ ≤ (L + C) * (a * ∑ j ∈ range (k + 1), a ^ j + 1) := by nlinarith

/-- The swap recurrence `F 0 ≤ L`, `F (k+1) ≤ a F k + C` with `a ≤ x` and `1 < x`
gives `F k ≤ K x^k` with the explicit constant `K = (L + C) x / (x - 1)`. -/
theorem swap_recurrence {F : ℕ → ℝ} {a x L C : ℝ} (ha : 0 ≤ a) (hx : 1 < x) (hax : a ≤ x)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hbase : F 0 ≤ L) (hstep : ∀ k, F (k + 1) ≤ a * F k + C) :
    ∀ k, F k ≤ (L + C) * x / (x - 1) * x ^ k := by
  intro k
  have hx1 : 0 < x - 1 := by linarith
  calc
    F k ≤ (L + C) * ∑ j ∈ range (k + 1), a ^ j := unroll ha hL hC hbase hstep k
    _ ≤ (L + C) * (x ^ (k + 1) / (x - 1)) := by
      gcongr
      exact geom_sum_le_of_le ha hx hax k
    _ = (L + C) * x / (x - 1) * x ^ k := by
      rw [pow_succ]
      field_simp

/-- With `x = m^τ`, the bound `x^k` is `(m^k)^τ`: a power of the chunk width. -/
theorem rpow_pow_eq (m : ℕ) (τ : ℝ) (k : ℕ) :
    ((m : ℝ) ^ τ) ^ k = ((m ^ k : ℕ) : ℝ) ^ τ := by
  push_cast
  rw [← Real.rpow_natCast ((m : ℝ) ^ τ) k, ← Real.rpow_mul (Nat.cast_nonneg m), mul_comm,
    Real.rpow_mul (Nat.cast_nonneg m), Real.rpow_natCast]

/-- The power-width bound in terms of the width `e = m^k`. -/
theorem power_width_bound {F : ℕ → ℝ} {m : ℕ} {a τ L C : ℝ} (hm : 2 ≤ m) (hτ : 0 < τ)
    (ha : 0 ≤ a) (hax : a ≤ (m : ℝ) ^ τ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbase : F 0 ≤ L) (hstep : ∀ k, F (k + 1) ≤ a * F k + C) :
    ∀ k, F k ≤ (L + C) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) * ((m ^ k : ℕ) : ℝ) ^ τ := by
  intro k
  have hx : 1 < (m : ℝ) ^ τ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < m by omega)) hτ
  rw [← rpow_pow_eq]
  exact swap_recurrence ha hx hax hL hC hbase hstep k

/-- Digit pieces: `Σ_j d_j (m^j)^τ ≤ (m - 1) x^(k+1) / (x - 1)` for digits `d_j < m`
and `x = m^τ`. -/
theorem digit_sum_le {m : ℕ} (hm : 2 ≤ m) {τ : ℝ} (hτ : 0 < τ) (d : ℕ → ℕ)
    (hd : ∀ j, d j < m) (k : ℕ) :
    ∑ j ∈ range (k + 1), (d j : ℝ) * ((m : ℝ) ^ τ) ^ j ≤
      ((m : ℝ) - 1) * ((m : ℝ) ^ τ) ^ (k + 1) / ((m : ℝ) ^ τ - 1) := by
  have hx : 1 < (m : ℝ) ^ τ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < m by omega)) hτ
  have hx0 : 0 ≤ (m : ℝ) ^ τ := by positivity
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    ∑ j ∈ range (k + 1), (d j : ℝ) * ((m : ℝ) ^ τ) ^ j
        ≤ ∑ j ∈ range (k + 1), ((m : ℝ) - 1) * ((m : ℝ) ^ τ) ^ j := by
      gcongr with j
      have h : (d j : ℝ) + 1 ≤ m := by exact_mod_cast hd j
      linarith
    _ = ((m : ℝ) - 1) * ∑ j ∈ range (k + 1), ((m : ℝ) ^ τ) ^ j := by rw [mul_sum]
    _ ≤ ((m : ℝ) - 1) * (((m : ℝ) ^ τ) ^ (k + 1) / ((m : ℝ) ^ τ - 1)) := by
      gcongr
      · linarith
      · exact geom_sum_le_of_le hx0 hx le_rfl k
    _ = _ := by ring

/-- The pieces of a width `n ≥ m^k` cost `O(n^τ)` in total. -/
theorem pieces_le {m : ℕ} (hm : 2 ≤ m) {τ : ℝ} (hτ : 0 < τ) (d : ℕ → ℕ)
    (hd : ∀ j, d j < m) {k n : ℕ} (hk : m ^ k ≤ n) :
    ∑ j ∈ range (k + 1), (d j : ℝ) * ((m ^ j : ℕ) : ℝ) ^ τ ≤
      ((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) * (n : ℝ) ^ τ := by
  have hx : 1 < (m : ℝ) ^ τ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < m by omega)) hτ
  have hm1 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : ((m ^ k : ℕ) : ℝ) ^ τ ≤ (n : ℝ) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) hτ.le
  calc
    ∑ j ∈ range (k + 1), (d j : ℝ) * ((m ^ j : ℕ) : ℝ) ^ τ
        = ∑ j ∈ range (k + 1), (d j : ℝ) * ((m : ℝ) ^ τ) ^ j := by
      apply sum_congr rfl
      intro j _
      rw [rpow_pow_eq]
    _ ≤ ((m : ℝ) - 1) * ((m : ℝ) ^ τ) ^ (k + 1) / ((m : ℝ) ^ τ - 1) :=
      digit_sum_le hm hτ d hd k
    _ = ((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) * ((m ^ k : ℕ) : ℝ) ^ τ := by
      rw [← rpow_pow_eq, pow_succ]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left hpow
        (div_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith))

/-- Base-`m` expansion of a width below `m^(k+1)` into digits `n / m^j % m`. -/
theorem base_expansion {m : ℕ} (hm : 2 ≤ m) :
    ∀ k n, n < m ^ (k + 1) → ∑ j ∈ range (k + 1), n / m ^ j % m * m ^ j = n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simp only [zero_add, range_one, sum_singleton, pow_zero, Nat.div_one, mul_one]
    exact Nat.mod_eq_of_lt (by simpa using hn)
  | succ k ih =>
    intro n hn
    have hdiv : n / m < m ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      rw [pow_succ] at hn
      exact hn
    have hrec := ih (n / m) hdiv
    rw [sum_range_succ']
    simp only [pow_zero, Nat.div_one, mul_one]
    have hshift : ∀ j, n / m ^ (j + 1) % m * m ^ (j + 1) =
        m * (n / m / m ^ j % m * m ^ j) := by
      intro j
      rw [pow_succ', Nat.div_div_eq_div_mul, mul_comm m (m ^ j)]
      ring
    simp_rw [hshift]
    rw [← mul_sum, hrec, add_comm]
    exact Nat.mod_add_div n m

theorem base_digit_lt {m : ℕ} (hm : 2 ≤ m) (n j : ℕ) : n / m ^ j % m < m :=
  Nat.mod_lt _ (by omega)

/-- Pad a row count `R` to the next multiple of `D ≤ R`; it stays below `2R`. -/
theorem row_padding {R D : ℕ} (hD : 0 < D) (hDR : D ≤ R) :
    D ∣ D * ((R + D - 1) / D) ∧ R ≤ D * ((R + D - 1) / D) ∧
      D * ((R + D - 1) / D) < 2 * R := by
  refine ⟨dvd_mul_right _ _, ?_, ?_⟩
  · have h := Nat.div_add_mod (R + D - 1) D
    have hmod := Nat.mod_lt (R + D - 1) hD
    set q := (R + D - 1) / D
    set r := (R + D - 1) % D
    omega
  · have h := Nat.mul_div_le (R + D - 1) D
    omega

/-- The row-range digit count `ρ = ⌈k log W / (2 log q)⌉` gives `q^(2ρ) ≥ W^k`. -/
theorem row_range {W q : ℕ} (hW : 1 ≤ W) (hq : 2 ≤ q) (k : ℕ) :
    W ^ k ≤ q ^ (2 * ⌈(k : ℝ) * Real.log W / (2 * Real.log q)⌉₊) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1
  set ρ := ⌈(k : ℝ) * Real.log W / (2 * Real.log q)⌉₊ with hρ
  have hceil : (k : ℝ) * Real.log W / (2 * Real.log q) ≤ ρ := Nat.le_ceil _
  have hmain : (k : ℝ) * Real.log W ≤ (2 * ρ : ℕ) * Real.log q := by
    push_cast
    rw [div_le_iff₀ (by positivity)] at hceil
    linarith
  have hpos : (0 : ℝ) < (W : ℝ) ^ k := by positivity
  have hpos' : (0 : ℝ) < (q : ℝ) ^ (2 * ρ) := by positivity
  have := (Real.log_le_log_iff hpos hpos').mp (by
    rw [Real.log_pow, Real.log_pow]
    exact hmain)
  exact_mod_cast this

/-- The row-range digit count is eventually below any width that grows like `e`,
when `k` is the base-`m` logarithm of `e` rounded up. -/
theorem row_range_small {m W q : ℕ} (hm : 2 ≤ m) (hW : 1 ≤ W) (hq : 2 ≤ q) :
    ∀ᶠ e : ℕ in Filter.atTop,
      ⌈(⌈Real.log e / Real.log m⌉₊ : ℝ) * Real.log W / (2 * Real.log q)⌉₊ < e := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  set c := Real.log W / (2 * Real.log q) with hc
  have hc0 : 0 ≤ c := by positivity
  -- `ρ ≤ (c / log m) log e + c + 1`, and `log e` is eventually below `ε e`.
  have hε : 0 < 1 / (2 * (c / Real.log m + 1)) := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.def hε
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      c / Real.log m * Real.log x + c + 2 ≤ x := by
    filter_upwards [hsmall, Filter.eventually_ge_atTop (2 * (c + 2)),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx2 hx1
    simp only [id, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)] at hx
    have hcm : 0 ≤ c / Real.log m := by positivity
    have h1 : c / Real.log m * Real.log x ≤ x / 2 := by
      calc c / Real.log m * Real.log x
          ≤ c / Real.log m * (1 / (2 * (c / Real.log m + 1)) * x) := by gcongr
        _ ≤ x / 2 := by
          rw [← mul_assoc]
          have hx0 : 0 ≤ x := by linarith
          have : c / Real.log m * (1 / (2 * (c / Real.log m + 1))) ≤ 1 / 2 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          nlinarith
    linarith
  have hnat := Filter.Tendsto.eventually (tendsto_natCast_atTop_atTop (R := ℝ)) hreal
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with e he he1
  have he1' : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hloge : 0 ≤ Real.log e := Real.log_nonneg he1'
  set k := ⌈Real.log e / Real.log m⌉₊ with hk
  have hkle : (k : ℝ) < Real.log e / Real.log m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hρ : ((k : ℝ) * Real.log W / (2 * Real.log q)) < c / Real.log m * Real.log e + c + 1 := by
    have : (k : ℝ) * Real.log W / (2 * Real.log q) = k * c := by rw [hc]; ring
    rw [this]
    have : c / Real.log m * Real.log e + c = (Real.log e / Real.log m + 1) * c := by
      field_simp
    rw [this]
    nlinarith [mul_lt_mul_of_pos_right hkle (by positivity : (0 : ℝ) < c + 1)]
  have hceil : (⌈(k : ℝ) * Real.log W / (2 * Real.log q)⌉₊ : ℝ) <
      (k : ℝ) * Real.log W / (2 * Real.log q) + 1 := Nat.ceil_lt_add_one (by positivity)
  have : (⌈(k : ℝ) * Real.log W / (2 * Real.log q)⌉₊ : ℝ) < e := by linarith
  exact_mod_cast this

theorem radixWidth_exists (q u : ℕ) : ∃ e, 2 ^ u ≤ (q + 2) ^ e :=
  ⟨u, Nat.pow_le_pow_left (by omega : 2 ≤ q + 2) u⟩

/-- The least radix-`(q+2)` width covering `[2^u]`. -/
def radixWidth (q u : ℕ) : ℕ := Nat.find (radixWidth_exists q u)

theorem radixWidth_spec (q u : ℕ) : 2 ^ u ≤ (q + 2) ^ radixWidth q u :=
  Nat.find_spec (radixWidth_exists q u)

theorem radixWidth_le (q u : ℕ) : radixWidth q u ≤ u :=
  Nat.find_min' (radixWidth_exists q u) (Nat.pow_le_pow_left (by omega : 2 ≤ q + 2) u)

/-- Padding each chunk range from `[2^u]` to `[q^e]` multiplies the range by less
than `q`, so two chunks increase the volume by less than `q²`. -/
theorem radixWidth_lt (q u : ℕ) : (q + 2) ^ radixWidth q u < (q + 2) * 2 ^ u := by
  rcases Nat.eq_zero_or_pos (radixWidth q u) with h | h
  · rw [h, pow_zero]
    have : 0 < 2 ^ u := by positivity
    nlinarith
  · have hmin : ¬ 2 ^ u ≤ (q + 2) ^ (radixWidth q u - 1) :=
      Nat.find_min (radixWidth_exists q u) (m := radixWidth q u - 1) (Nat.sub_one_lt h.ne')
    push Not at hmin
    have : (q + 2) ^ radixWidth q u = (q + 2) * (q + 2) ^ (radixWidth q u - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel h]
    rw [this]
    exact Nat.mul_lt_mul_of_pos_left hmin (by omega)

end IntegerMultBounds.Swap.Recurrence
