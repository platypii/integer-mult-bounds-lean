import IntegerMultBounds.Resampling.PiApprox
import IntegerMultBounds.Resampling.ExpApprox
import IntegerMultBounds.Resampling.TabledMaps

/-! Integer weight tables for the numerical maps, computed from the certified
approximations of `π` and `exp`: with `q = 5p` guard bits, `P ≈ 2^q π`,
`Y = ⌊P a / b⌋ ≈ 2^q π a/b`, the Taylor sum of `exp (± Y / 2^q)` with `7p`
terms, shifted down by `4p` bits, is within `3/2` of `2^p exp (± π a/b)`
(with a shortcut to zero when the negative exponent is below `-p`). The three
tables of the Gaussian, off-diagonal and diagonal weights follow, each within
two units. -/

namespace IntegerMultBounds.Resampling.WeightTable

open Real Finset Nat
open PiApprox (piApprox piApprox_err)
open ExpApprox (expApprox expApprox_err ediv_err)

/-- `2^(5p) π`, approximately. -/
def piQ (p : ℕ) : ℤ := piApprox (5 * p) (5 * p)

/-- `2^p exp (-π a/b)` (`neg`) or `2^p exp (π a/b)`, approximately. -/
def expPi (neg : Bool) (p a b : ℕ) : ℤ :=
  let Y : ℤ := (piQ p * a) / b
  if neg then (if (p : ℤ) * 2 ^ (5 * p) ≤ Y then 0 else expApprox (-Y) (5 * p) (7 * p) / 2 ^ (4 * p))
  else expApprox Y (5 * p) (7 * p) / 2 ^ (4 * p)

section Lemmas

theorem piQ_err (p : ℕ) (hp : 1 ≤ p) : |(piQ p : ℝ) - 2 ^ (5 * p) * π| ≤ 20 * (5 * p) + 1 := by
  have h := piApprox_err (5 * p) (5 * p)
  have h5 : 40 * (2 : ℝ) ^ (5 * p) * (1 / 5 : ℝ) ^ (2 * (5 * p) + 1) ≤ 1 := by
    rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
    have : (40 : ℝ) * 2 ^ (5 * p) ≤ 5 ^ (2 * (5 * p) + 1) := by
      have h1 : (2 : ℝ) ^ (5 * p) ≤ 5 ^ (5 * p) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have h2 : (40 : ℝ) ≤ 5 ^ (5 * p + 1) := by
        calc (40 : ℝ) ≤ 5 ^ 6 := by norm_num
          _ ≤ 5 ^ (5 * p + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (40 : ℝ) * 2 ^ (5 * p) ≤ 5 ^ (5 * p + 1) * 5 ^ (5 * p) := by
            gcongr
        _ = 5 ^ (2 * (5 * p) + 1) := by rw [← pow_add]; ring_nf
    exact this
  unfold piQ
  push_cast at h ⊢
  linarith

theorem abs_exp_sub_le_of_nonpos {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) : |exp u - exp v| ≤ |u - v| := by
  wlog h : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hv hu (by linarith)
  have e1 : exp v - exp u = exp v * (1 - exp (u - v)) := by
    rw [mul_sub, mul_one, ← exp_add]; ring_nf
  have h1 : 1 - exp (u - v) ≤ v - u := by have := add_one_le_exp (u - v); linarith
  have h2 : 0 ≤ 1 - exp (u - v) := by
    have : exp (u - v) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  have h3 : exp v ≤ 1 := exp_le_one_iff.mpr hv
  rw [abs_sub_comm, abs_of_nonneg (by rw [e1]; exact mul_nonneg (exp_pos v).le h2), abs_of_nonpos (by linarith), e1]
  nlinarith [exp_pos v]

theorem abs_exp_sub_le_of_le {u v M : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    |exp u - exp v| ≤ exp M * |u - v| := by
  wlog h : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hv hu (by linarith)
  have e1 : exp v - exp u = exp v * (1 - exp (u - v)) := by
    rw [mul_sub, mul_one, ← exp_add]; ring_nf
  have h1 : 1 - exp (u - v) ≤ v - u := by have := add_one_le_exp (u - v); linarith
  have h2 : 0 ≤ 1 - exp (u - v) := by
    have : exp (u - v) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  have h3 : exp v ≤ exp M := exp_le_exp.mpr hv
  rw [abs_sub_comm, abs_of_nonneg (by rw [e1]; exact mul_nonneg (exp_pos v).le h2), abs_of_nonpos (by linarith), e1]
  nlinarith [exp_pos v, exp_pos M]

/-- `L^(2L+j)/(2L+j)! ≤ e^L 2^-j`. -/
theorem pow_div_fact_le (L j : ℕ) :
    (L : ℝ) ^ (2 * L + j) / ((2 * L + j)! : ℝ) ≤ exp L * (1 / 2) ^ j := by
  induction j with
  | zero =>
    simp only [add_zero, pow_zero, mul_one]
    calc (L : ℝ) ^ (2 * L) / ((2 * L)! : ℝ) ≤ ∑ i ∈ range (2 * L + 1), (L : ℝ) ^ i / (i ! : ℝ) :=
          single_le_sum (f := fun i => (L : ℝ) ^ i / (i ! : ℝ)) (fun i _ => by positivity)
            (mem_range.mpr (by omega))
      _ ≤ exp L := sum_le_exp_of_nonneg (by positivity) _
  | succ j ih =>
    have hf : ((2 * L + (j + 1))! : ℝ) = (2 * L + j + 1) * ((2 * L + j)! : ℝ) := by
      rw [show 2 * L + (j + 1) = (2 * L + j) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hpos : (0 : ℝ) < ((2 * L + j)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hL : (L : ℝ) / (2 * L + j + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc (L : ℝ) ^ (2 * L + (j + 1)) / ((2 * L + (j + 1))! : ℝ)
        = (L : ℝ) ^ (2 * L + j) / ((2 * L + j)! : ℝ) * ((L : ℝ) / (2 * L + j + 1)) := by
          rw [hf, show 2 * L + (j + 1) = (2 * L + j) + 1 by ring, pow_succ]; field_simp
      _ ≤ exp L * (1 / 2) ^ j * (1 / 2) := by gcongr
      _ = exp L * (1 / 2) ^ (j + 1) := by ring

end Lemmas

section Numerics

theorem fdiv_err (a b : ℤ) (hb : 0 < b) : |((a / b : ℤ) : ℝ) - (a : ℝ) / b| ≤ 1 := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.emod_nonneg a hb.ne'
  have h3 := Int.emod_lt_of_pos a hb
  have e : (a : ℝ) = b * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by exact_mod_cast h1.symm
  have h2' : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((a % b : ℤ) : ℝ) < b := by exact_mod_cast h3
  rw [abs_le]; constructor
  · rw [neg_le_sub_iff_le_add, div_le_iff₀ hbr]; nlinarith
  · have : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by rw [le_div_iff₀ hbr]; nlinarith
    linarith

theorem exp_le_three_pow (x : ℕ) : exp (x : ℝ) ≤ 3 ^ x := by
  rw [← exp_one_rpow, Real.rpow_natCast]
  exact pow_le_pow_left₀ (exp_pos 1).le (by have := exp_one_lt_d9; linarith) x

theorem nine_le (p : ℕ) (hp : 13 ≤ p) : 8 * 9 ^ p ≤ 16 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ, pow_succ]; omega

theorem three_le (p : ℕ) (hp : 13 ≤ p) : 8 * (7 * p * 3 ^ p) ≤ 16 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    have : 8 * (7 * (n + 1) * (3 ^ n * 3)) ≤ 16 * (8 * (7 * n * 3 ^ n)) := by nlinarith [Nat.one_le_pow n 3 (by norm_num)]
    omega

theorem poly_le (p : ℕ) (hp : 13 ≤ p) : 8 * (3 ^ p * (100 * p * p + p + 2)) ≤ 16 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    have hX : 3 * (100 * (n + 1) * (n + 1) + (n + 1) + 2) ≤ 16 * (100 * n * n + n + 2) := by nlinarith
    have : 8 * (3 ^ n * 3 * (100 * (n + 1) * (n + 1) + (n + 1) + 2)) ≤
        16 * (8 * (3 ^ n * (100 * n * n + n + 2))) := by
      calc 8 * (3 ^ n * 3 * (100 * (n + 1) * (n + 1) + (n + 1) + 2))
          = 8 * 3 ^ n * (3 * (100 * (n + 1) * (n + 1) + (n + 1) + 2)) := by ring
        _ ≤ 8 * 3 ^ n * (16 * (100 * n * n + n + 2)) := Nat.mul_le_mul_left _ hX
        _ = 16 * (8 * (3 ^ n * (100 * n * n + n + 2))) := by ring
    omega

theorem two_pow_le (p : ℕ) (hp : 2 ≤ p) : (2 : ℝ) ^ p ≤ 3 / 2 * (27 / 10) ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 27 / 10) (n - 1)]

end Numerics

section Core

variable (p a b : ℕ) (hp : 13 ≤ p) (hb : 0 < b)

/-- `Y = ⌊P a / b⌋` is within `1 + (a/b)(20q+1)` of `2^q π a/b`. -/
theorem Y_close (hp1 : 1 ≤ p) (hb : 0 < b) :
    |(((piQ p * a) / b : ℤ) : ℝ) - 2 ^ (5 * p) * π * a / b| ≤ 1 + (a : ℝ) / b * (20 * (5 * p) + 1) := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := fdiv_err (piQ p * a) b (by exact_mod_cast hb)
  have h2 := piQ_err p hp1
  push_cast at h1
  have e : ((piQ p : ℝ) * a / b) - 2 ^ (5 * p) * π * a / b = (a / b) * ((piQ p : ℝ) - 2 ^ (5 * p) * π) := by
    field_simp
  have h3 : |((piQ p : ℝ) * a / b) - 2 ^ (5 * p) * π * a / b| ≤ (a : ℝ) / b * (20 * (5 * p) + 1) := by
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
  calc _ ≤ |(((piQ p * a) / b : ℤ) : ℝ) - (piQ p : ℝ) * a / b| + |((piQ p : ℝ) * a / b) - 2 ^ (5 * p) * π * a / b| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

theorem lin_le_pow (q : ℕ) (hq : 8 ≤ q) : 20 * q + 1 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

theorem piQ_nonneg (hp2 : 2 ≤ p) : 0 ≤ piQ p := by
  have h := piQ_err p (by omega)
  have hpi := pi_gt_three
  have h2 : (20 * (5 * (p : ℝ)) + 1) ≤ 2 ^ (5 * p) := by
    have := lin_le_pow (5 * p) (by omega)
    exact_mod_cast this
  have : (0 : ℝ) ≤ piQ p := by
    rw [abs_le] at h
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (5 * p)]
  exact_mod_cast this

end Core

section Main

theorem lin100 (p : ℕ) (hp : 2 ≤ p) : 100 * p + 1 ≤ 2 ^ (4 * p) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [show 4 * (n + 1) = 4 * n + 4 by ring, pow_add]; omega

theorem p_le_half (p : ℕ) (hp : 1 ≤ p) : (p : ℝ) ≤ 2 ^ p / 2 := by
  have : 2 * p ≤ 2 ^ p := by
    induction p, hp using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  have h : (2 * p : ℝ) ≤ 2 ^ p := by exact_mod_cast this
  linarith

/-- The sum of the three error terms of the core computation is at most half of `16^p`. -/
theorem err_sum (p : ℕ) (hp : 13 ≤ p) :
    7 * p * (3 : ℝ) ^ p + 9 ^ p + (1 + p * (20 * (5 * p) + 1)) ≤ 16 ^ p / 2 := by
  have h1 : (8 * 9 ^ p : ℝ) ≤ 16 ^ p := by exact_mod_cast nine_le p hp
  have h2 : (8 * (7 * p * 3 ^ p) : ℝ) ≤ 16 ^ p := by exact_mod_cast three_le p hp
  have h3 : (8 * (3 ^ p * (100 * p * p + p + 2)) : ℝ) ≤ 16 ^ p := by exact_mod_cast poly_le p hp
  have h4 : (1 : ℝ) ≤ 3 ^ p := one_le_pow₀ (by norm_num)
  have h5 : (1 + p * (20 * (5 * p) + 1) : ℝ) ≤ 3 ^ p * (100 * p * p + p + 2) := by
    nlinarith [sq_nonneg (p : ℝ)]
  have h6 : (0 : ℝ) ≤ 16 ^ p := by positivity
  nlinarith

theorem expPi_neg_err (p a b : ℕ) (hp : 13 ≤ p) (hb : 0 < b) :
    |(expPi true p a b : ℝ) - 2 ^ p * exp (-(π * a / b))| ≤ 3 / 2 := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : (2 : ℝ) ^ (5 * p) = 2 ^ (4 * p) * 2 ^ p := by rw [← pow_add]; ring_nf
  have h4p : (0 : ℝ) < 2 ^ (4 * p) := by positivity
  have h20 : (20 * (5 * p) + 1 : ℝ) ≤ 2 ^ (4 * p) := by
    have := lin100 p (by omega); exact_mod_cast (by omega : 20 * (5 * p) + 1 ≤ 2 ^ (4 * p))
  set Y : ℤ := (piQ p * a) / b with hYdef
  have hY := Y_close p a b (by omega) hb
  rw [← hYdef] at hY
  have hY0 : (0 : ℤ) ≤ Y := Int.ediv_nonneg (mul_nonneg (piQ_nonneg p (by omega)) (by positivity)) (by positivity)
  have hab : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hpi := pi_gt_three
  have hhalf := p_le_half p (by omega)
  by_cases hs : (p : ℤ) * 2 ^ (5 * p) ≤ Y
  · have hW : expPi true p a b = 0 := by simp [expPi, ← hYdef, hs]
    rw [hW, Int.cast_zero, zero_sub, abs_neg, abs_of_pos (by positivity)]
    have hs' : (p : ℝ) * 2 ^ (5 * p) ≤ Y := by exact_mod_cast hs
    -- π a / b ≥ p - 1
    have hge : (p : ℝ) - 1 ≤ π * a / b := by
      by_contra hlt
      push Not at hlt
      have hab' : (a : ℝ) / b ≤ p := by
        have : π * ((a : ℝ) / b) < p := by rw [← mul_div_assoc]; linarith
        nlinarith
      rw [abs_le] at hY
      have : (Y : ℝ) ≤ 2 ^ (5 * p) * π * a / b + 1 + (a : ℝ) / b * (20 * (5 * p) + 1) := by linarith
      have e1 : 2 ^ (5 * p) * π * (a : ℝ) / b = 2 ^ (5 * p) * (π * a / b) := by ring
      have e2 : (a : ℝ) / b * (20 * (5 * p) + 1) ≤ p * 2 ^ (4 * p) := by
        calc (a : ℝ) / b * (20 * (5 * p) + 1) ≤ p * 2 ^ (4 * p) := by gcongr
          _ = p * 2 ^ (4 * p) := rfl
      have e3 : (p : ℝ) * 2 ^ (4 * p) ≤ 2 ^ (5 * p) / 2 := by
        rw [hq]; nlinarith
      have e4 : (1 : ℝ) < 2 ^ (5 * p) / 2 := by
        have : (4 : ℝ) ≤ 2 ^ (5 * p) := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (5 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have e5 : 2 ^ (5 * p) * (π * a / b) < 2 ^ (5 * p) * ((p : ℝ) - 1) := by
        exact mul_lt_mul_of_pos_left hlt (by positivity)
      nlinarith
    have hexp : exp (-(π * a / b)) ≤ exp (1 - p) := exp_le_exp.mpr (by linarith)
    have he : (27 / 10 : ℝ) ^ (p - 1) ≤ exp ((p : ℝ) - 1) := by
      rw [show ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) by push_cast [show 1 ≤ p by omega]; ring, ← exp_one_rpow,
        Real.rpow_natCast]
      exact pow_le_pow_left₀ (by norm_num) (by have := exp_one_gt_d9; linarith) _
    have h2 := two_pow_le p (by omega)
    have hexp' : exp (1 - (p : ℝ)) = (exp ((p : ℝ) - 1))⁻¹ := by rw [← exp_neg]; ring_nf
    calc 2 ^ p * exp (-(π * a / b)) ≤ 2 ^ p * exp (1 - p) := by gcongr
      _ = 2 ^ p / exp ((p : ℝ) - 1) := by rw [hexp', div_eq_mul_inv]
      _ ≤ 3 / 2 * (27 / 10) ^ (p - 1) / (27 / 10) ^ (p - 1) := by
          gcongr
      _ = 3 / 2 := by field_simp
  · push Not at hs
    have hW : expPi true p a b = expApprox (-Y) (5 * p) (7 * p) / 2 ^ (4 * p) := by
      simp [expPi, ← hYdef, not_le.mpr hs]
    have hs' : (Y : ℝ) < p * 2 ^ (5 * p) := by exact_mod_cast hs
    have hY0' : (0 : ℝ) ≤ Y := by exact_mod_cast hY0
    have h4q : (2 : ℝ) ^ (4 * p) ≤ 2 ^ (5 * p) / 2 := by
      rw [hq]; have : (2 : ℝ) ≤ 2 ^ p := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hq0 : (0 : ℝ) < 2 ^ (5 * p) := by positivity
    -- a / b ≤ p
    have hab_le : (a : ℝ) / b ≤ p := by
      by_contra hgt
      push Not at hgt
      rw [abs_le] at hY
      have e1 : 2 ^ (5 * p) * π * (a : ℝ) / b = 2 ^ (5 * p) * ((a : ℝ) / b) * π := by ring
      have e2 : (a : ℝ) / b * (20 * (5 * p) + 1) ≤ (a : ℝ) / b * (2 ^ (5 * p) / 2) := by
        gcongr; linarith
      have e3 : (1 : ℝ) ≤ 2 ^ (5 * p) := one_le_pow₀ (by norm_num)
      have k1 : 2 ^ (5 * p) * π * (a : ℝ) / b - 1 - (a : ℝ) / b * (20 * (5 * p) + 1) ≤ Y := by linarith [hY.1]
      have k3 : (a : ℝ) / b * 2 ^ (5 * p) * (π - 1 / 2) < (p + 1) * 2 ^ (5 * p) := by
        rw [e1] at k1; nlinarith
      have k4 : (a : ℝ) / b * (π - 1 / 2) < p + 1 := by
        by_contra hc
        push Not at hc
        have : (p + 1) * 2 ^ (5 * p) ≤ (a : ℝ) / b * (π - 1 / 2) * 2 ^ (5 * p) :=
          mul_le_mul_of_nonneg_right hc hq0.le
        linarith
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
      nlinarith
    set xt : ℝ := (((-Y : ℤ)) : ℝ) / 2 ^ (5 * p) with hxt
    have hxt0 : xt ≤ 0 := by rw [hxt]; push_cast; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le
    have hxtp : |xt| ≤ p := by
      rw [hxt, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]; push_cast
      rw [abs_neg, abs_of_nonneg hY0']; linarith
    have hE := expApprox_err (-Y) (5 * p) (7 * p)
    rw [← hxt] at hE
    have hexpx : exp |xt| ≤ 3 ^ p := (exp_le_exp.mpr hxtp).trans (exp_le_three_pow p)
    have hpow : |xt| ^ (7 * p) / ((7 * p)! : ℝ) ≤ exp p * (1 / 2) ^ (5 * p) := by
      have h := pow_div_fact_le p (5 * p)
      rw [show 2 * p + 5 * p = 7 * p by ring] at h
      refine le_trans ?_ h
      gcongr
    have hep : exp (p : ℝ) ≤ 3 ^ p := exp_le_three_pow p
    have hhalfpow : (2 : ℝ) ^ (5 * p) * (1 / 2) ^ (5 * p) = 1 := by rw [← mul_pow]; norm_num
    have hEb : |(expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt| ≤ 7 * p * 3 ^ p + 9 ^ p := by
      refine hE.trans ?_
      have t1 : ((7 * p : ℕ) : ℝ) * exp |xt| ≤ 7 * p * 3 ^ p := by push_cast; gcongr
      have t2 : 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p)! : ℝ) * exp |xt|) ≤ 9 ^ p := by
        calc 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p)! : ℝ) * exp |xt|)
            ≤ 2 ^ (5 * p) * (exp p * (1 / 2) ^ (5 * p) * 3 ^ p) := by gcongr
          _ = (2 ^ (5 * p) * (1 / 2) ^ (5 * p)) * exp p * 3 ^ p := by ring
          _ ≤ 1 * 3 ^ p * 3 ^ p := by rw [hhalfpow]; gcongr
          _ = 9 ^ p := by rw [one_mul, ← mul_pow]; norm_num
      linarith
    have hclose : |exp xt - exp (-(π * a / b))| ≤ (1 + p * (20 * (5 * p) + 1)) / 2 ^ (5 * p) := by
      refine (abs_exp_sub_le_of_nonpos hxt0 (by have h0 : 0 ≤ π * a / b := (by positivity); linarith)).trans ?_
      rw [hxt, le_div_iff₀ hq0]
      have e : ((((-Y : ℤ)) : ℝ) / 2 ^ (5 * p) - -(π * a / b)) * 2 ^ (5 * p) =
          -((Y : ℝ) - 2 ^ (5 * p) * π * a / b) := by push_cast; field_simp; ring
      rw [← abs_of_pos hq0, ← abs_mul, abs_of_pos hq0, e, abs_neg]
      calc _ ≤ 1 + (a : ℝ) / b * (20 * (5 * p) + 1) := hY
        _ ≤ 1 + p * (20 * (5 * p) + 1) := by gcongr
    have hsum := err_sum p hp
    have h16 : (16 : ℝ) ^ p = 2 ^ (4 * p) := by rw [pow_mul]; norm_num
    have hEx : |(expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (-(π * a / b))| ≤ 2 ^ (4 * p) / 2 := by
      have e : (expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (-(π * a / b)) =
          ((expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt) +
            2 ^ (5 * p) * (exp xt - exp (-(π * a / b))) := by ring
      rw [e]
      calc _ ≤ |(expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt| +
            |2 ^ (5 * p) * (exp xt - exp (-(π * a / b)))| := abs_add_le _ _
        _ ≤ (7 * p * 3 ^ p + 9 ^ p) + (1 + p * (20 * (5 * p) + 1)) := by
            gcongr
            rw [abs_mul, abs_of_pos hq0]
            calc 2 ^ (5 * p) * |exp xt - exp (-(π * a / b))| ≤
                2 ^ (5 * p) * ((1 + p * (20 * (5 * p) + 1)) / 2 ^ (5 * p)) := by gcongr
              _ = 1 + p * (20 * (5 * p) + 1) := by field_simp
        _ ≤ 2 ^ (4 * p) / 2 := by rw [← h16]; linarith
    have hdiv := fdiv_err (expApprox (-Y) (5 * p) (7 * p)) (2 ^ (4 * p)) (by positivity)
    rw [Int.cast_pow, Int.cast_ofNat] at hdiv
    rw [hW]
    have e : ((expApprox (-Y) (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - 2 ^ p * exp (-(π * a / b)) =
        (((expApprox (-Y) (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - (expApprox (-Y) (5 * p) (7 * p) : ℝ) / 2 ^ (4 * p)) +
          ((expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (-(π * a / b))) / 2 ^ (4 * p) := by
      rw [hq]; field_simp; ring
    rw [e]
    calc _ ≤ |(((expApprox (-Y) (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - (expApprox (-Y) (5 * p) (7 * p) : ℝ) / 2 ^ (4 * p))| +
          |((expApprox (-Y) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (-(π * a / b))) / 2 ^ (4 * p)| := abs_add_le _ _
      _ ≤ 1 + (2 ^ (4 * p) / 2) / 2 ^ (4 * p) := by
          refine add_le_add hdiv ?_
          rw [abs_div, abs_of_pos h4p]; gcongr
      _ = 3 / 2 := by field_simp; norm_num

theorem err_sum2 (p : ℕ) (hp : 13 ≤ p) :
    7 * p * (3 : ℝ) ^ p + 9 ^ p + 3 ^ p * (1 + p * (20 * (5 * p) + 1)) ≤ 16 ^ p / 2 := by
  have h1 : (8 * 9 ^ p : ℝ) ≤ 16 ^ p := by exact_mod_cast nine_le p hp
  have h2 : (8 * (7 * p * 3 ^ p) : ℝ) ≤ 16 ^ p := by exact_mod_cast three_le p hp
  have h3 : (8 * (3 ^ p * (100 * p * p + p + 2)) : ℝ) ≤ 16 ^ p := by exact_mod_cast poly_le p hp
  have h5 : (3 : ℝ) ^ p * (1 + p * (20 * (5 * p) + 1)) ≤ 3 ^ p * (100 * p * p + p + 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  have h6 : (0 : ℝ) ≤ 16 ^ p := by positivity
  nlinarith

theorem expPi_pos_err (p a b : ℕ) (hp : 13 ≤ p) (hb : 0 < b) (hx : π * a / b ≤ p - 1) :
    |(expPi false p a b : ℝ) - 2 ^ p * exp (π * a / b)| ≤ 3 / 2 := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : (2 : ℝ) ^ (5 * p) = 2 ^ (4 * p) * 2 ^ p := by rw [← pow_add]; ring_nf
  have h4p : (0 : ℝ) < 2 ^ (4 * p) := by positivity
  have hq0 : (0 : ℝ) < 2 ^ (5 * p) := by positivity
  set Y : ℤ := (piQ p * a) / b with hYdef
  have hY := Y_close p a b (by omega) hb
  rw [← hYdef] at hY
  have hY0 : (0 : ℤ) ≤ Y := Int.ediv_nonneg (mul_nonneg (piQ_nonneg p (by omega)) (by positivity)) (by positivity)
  have hY0' : (0 : ℝ) ≤ Y := by exact_mod_cast hY0
  have hpi := pi_gt_three
  have hab : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hab_le : (a : ℝ) / b ≤ p := by
    have : π * ((a : ℝ) / b) ≤ p - 1 := by rw [← mul_div_assoc]; exact hx
    nlinarith
  have hW : expPi false p a b = expApprox Y (5 * p) (7 * p) / 2 ^ (4 * p) := by simp [expPi, ← hYdef]
  set xt : ℝ := (Y : ℝ) / 2 ^ (5 * p) with hxt
  have hδ : |xt - π * a / b| ≤ (1 + p * (20 * (5 * p) + 1)) / 2 ^ (5 * p) := by
    rw [hxt, le_div_iff₀ hq0]
    have e : ((Y : ℝ) / 2 ^ (5 * p) - π * a / b) * 2 ^ (5 * p) = (Y : ℝ) - 2 ^ (5 * p) * π * a / b := by
      field_simp
    rw [← abs_of_pos hq0, ← abs_mul, abs_of_pos hq0, e]
    calc _ ≤ 1 + (a : ℝ) / b * (20 * (5 * p) + 1) := hY
      _ ≤ 1 + p * (20 * (5 * p) + 1) := by gcongr
  have hsmall : (1 + p * (20 * (5 * p) + 1) : ℝ) / 2 ^ (5 * p) ≤ 1 := by
    rw [div_le_one hq0]
    have h16 := err_sum2 p hp
    have : (16 : ℝ) ^ p ≤ 2 ^ (5 * p) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (1 : ℝ) ≤ 3 ^ p := one_le_pow₀ (by norm_num)
    have hpl : (8 * (3 ^ p * (100 * p * p + p + 2)) : ℝ) ≤ 16 ^ p := by exact_mod_cast poly_le p hp
    have hpoly : (1 + p * (20 * (5 * p) + 1) : ℝ) ≤ 3 ^ p * (100 * p * p + p + 2) := by
      have h0 : (1 + p * (20 * (5 * p) + 1) : ℝ) ≤ 100 * p * p + p + 2 := by nlinarith
      nlinarith [show (0 : ℝ) ≤ 100 * p * p + p + 2 by positivity]
    linarith
  have hxtp : |xt| ≤ p := by
    rw [abs_of_nonneg (by rw [hxt]; positivity)]
    have := (abs_le.mp hδ).2
    linarith
  have hE := expApprox_err Y (5 * p) (7 * p)
  rw [← hxt] at hE
  have hexpx : exp |xt| ≤ 3 ^ p := (exp_le_exp.mpr hxtp).trans (exp_le_three_pow p)
  have hpow : |xt| ^ (7 * p) / ((7 * p)! : ℝ) ≤ exp p * (1 / 2) ^ (5 * p) := by
    have h := pow_div_fact_le p (5 * p)
    rw [show 2 * p + 5 * p = 7 * p by ring] at h
    refine le_trans ?_ h
    gcongr
  have hep : exp (p : ℝ) ≤ 3 ^ p := exp_le_three_pow p
  have hhalfpow : (2 : ℝ) ^ (5 * p) * (1 / 2) ^ (5 * p) = 1 := by rw [← mul_pow]; norm_num
  have hEb : |(expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt| ≤ 7 * p * 3 ^ p + 9 ^ p := by
    refine hE.trans ?_
    have t1 : ((7 * p : ℕ) : ℝ) * exp |xt| ≤ 7 * p * 3 ^ p := by push_cast; gcongr
    have t2 : 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p)! : ℝ) * exp |xt|) ≤ 9 ^ p := by
      calc 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p)! : ℝ) * exp |xt|)
          ≤ 2 ^ (5 * p) * (exp p * (1 / 2) ^ (5 * p) * 3 ^ p) := by gcongr
        _ = (2 ^ (5 * p) * (1 / 2) ^ (5 * p)) * exp p * 3 ^ p := by ring
        _ ≤ 1 * 3 ^ p * 3 ^ p := by rw [hhalfpow]; gcongr
        _ = 9 ^ p := by rw [one_mul, ← mul_pow]; norm_num
    linarith
  have hxp : π * a / b ≤ p := by linarith
  have hclose : |exp xt - exp (π * a / b)| ≤ 3 ^ p * ((1 + p * (20 * (5 * p) + 1)) / 2 ^ (5 * p)) := by
    refine (abs_exp_sub_le_of_le (le_trans (le_abs_self xt) hxtp) hxp).trans ?_
    gcongr
  have h16 : (16 : ℝ) ^ p = 2 ^ (4 * p) := by rw [pow_mul]; norm_num
  have hsum := err_sum2 p hp
  have hEx : |(expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (π * a / b)| ≤ 2 ^ (4 * p) / 2 := by
    have e : (expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (π * a / b) =
        ((expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt) +
          2 ^ (5 * p) * (exp xt - exp (π * a / b)) := by ring
    rw [e]
    calc _ ≤ |(expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp xt| +
          |2 ^ (5 * p) * (exp xt - exp (π * a / b))| := abs_add_le _ _
      _ ≤ (7 * p * 3 ^ p + 9 ^ p) + 3 ^ p * (1 + p * (20 * (5 * p) + 1)) := by
          gcongr
          rw [abs_mul, abs_of_pos hq0]
          calc 2 ^ (5 * p) * |exp xt - exp (π * a / b)| ≤
              2 ^ (5 * p) * (3 ^ p * ((1 + p * (20 * (5 * p) + 1)) / 2 ^ (5 * p))) := by gcongr
            _ = 3 ^ p * (1 + p * (20 * (5 * p) + 1)) := by field_simp
      _ ≤ 2 ^ (4 * p) / 2 := by rw [← h16]; linarith
  have hdiv := fdiv_err (expApprox Y (5 * p) (7 * p)) (2 ^ (4 * p)) (by positivity)
  rw [Int.cast_pow, Int.cast_ofNat] at hdiv
  rw [hW]
  have e : ((expApprox Y (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - 2 ^ p * exp (π * a / b) =
      (((expApprox Y (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - (expApprox Y (5 * p) (7 * p) : ℝ) / 2 ^ (4 * p)) +
        ((expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (π * a / b)) / 2 ^ (4 * p) := by
    rw [hq]; field_simp; ring
  rw [e]
  calc _ ≤ |(((expApprox Y (5 * p) (7 * p) / 2 ^ (4 * p) : ℤ) : ℝ) - (expApprox Y (5 * p) (7 * p) : ℝ) / 2 ^ (4 * p))| +
        |((expApprox Y (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (π * a / b)) / 2 ^ (4 * p)| := abs_add_le _ _
    _ ≤ 1 + (2 ^ (4 * p) / 2) / 2 ^ (4 * p) := by
        refine add_le_add hdiv ?_
        rw [abs_div, abs_of_pos h4p]; gcongr
    _ = 3 / 2 := by field_simp; norm_num

end Main

section Tables

open IntegerMultBounds.NLogN (resampWeight normExp dPrime beta dCoef frac nearest)

/-- The Gaussian weight table: `⌊expPi (−π (sk − tj)²/(α²t²)) / α⌋`. -/
def tableA (s t α p : ℕ) (k : ZMod t) (j : ℤ) : ℤ :=
  expPi true p (((s : ℤ) * k.val - t * j) ^ 2).toNat (α ^ 2 * t ^ 2) / α

theorem tableA_err (s t α p : ℕ) [NeZero s] [NeZero t] (hp : 13 ≤ p) (hα : 2 ≤ α) (k : ZMod t) (j : ℤ) :
    |(tableA s t α p k j : ℝ) - 2 ^ p * resampWeight s t α k j| ≤ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have hα0 : (0 : ℝ) < α := by exact_mod_cast (by omega : 0 < α)
  have hb : 0 < α ^ 2 * t ^ 2 := Nat.mul_pos (pow_pos (by omega) 2) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne t)) 2)
  have hW := expPi_neg_err p (((s : ℤ) * k.val - t * j) ^ 2).toNat (α ^ 2 * t ^ 2) hp hb
  have ha : ((((s : ℤ) * k.val - t * j) ^ 2).toNat : ℝ) = ((s : ℝ) * k.val - t * j) ^ 2 := by
    rw [show ((((s : ℤ) * k.val - t * j) ^ 2).toNat : ℝ) = ((((s : ℤ) * k.val - t * j) ^ 2 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (sq_nonneg _)]
    push_cast; ring
  have hexp : resampWeight s t α k j = (1 / α) * exp (-(π * (((((s : ℤ) * k.val - t * j) ^ 2).toNat : ℕ) : ℝ) /
      ((α ^ 2 * t ^ 2 : ℕ) : ℝ))) := by
    unfold resampWeight
    rw [ha]
    congr 2
    push_cast
    field_simp
  rw [hexp]
  set W := expPi true p (((s : ℤ) * k.val - t * j) ^ 2).toNat (α ^ 2 * t ^ 2)
  set e := exp (-(π * (((((s : ℤ) * k.val - t * j) ^ 2).toNat : ℕ) : ℝ) / ((α ^ 2 * t ^ 2 : ℕ) : ℝ)))
  have hdiv := fdiv_err W α (by exact_mod_cast (by omega : 0 < α))
  push_cast at hdiv
  unfold tableA
  have e1 : ((W / (α : ℤ) : ℤ) : ℝ) - 2 ^ p * (1 / α * e) =
      (((W / (α : ℤ) : ℤ) : ℝ) - (W : ℝ) / α) + ((W : ℝ) - 2 ^ p * e) / α := by
    field_simp; ring
  rw [e1]
  have hα2 : (2 : ℝ) ≤ α := by exact_mod_cast hα
  calc _ ≤ |((W / (α : ℤ) : ℤ) : ℝ) - (W : ℝ) / α| + |((W : ℝ) - 2 ^ p * e) / α| := abs_add_le _ _
    _ ≤ 1 + (3 / 2) / 2 := by
        refine add_le_add hdiv ?_
        rw [abs_div, abs_of_pos hα0]
        calc |(W : ℝ) - 2 ^ p * e| / α ≤ (3 / 2) / α := by gcongr
          _ ≤ (3 / 2) / 2 := by gcongr
    _ ≤ 2 := by norm_num

theorem floor_div_int (n : ℤ) (d : ℕ) (hd : 0 < d) : ⌊(n : ℝ) / d⌋ = n / (d : ℤ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have h1 := Int.mul_ediv_add_emod n d
  have h2 := Int.emod_nonneg n hdz.ne'
  have h3 := Int.emod_lt_of_pos n hdz
  have e : (n : ℝ) = d * ((n / (d : ℤ) : ℤ) : ℝ) + ((n % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1.symm
  have h2' : (0 : ℝ) ≤ ((n % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((n % (d : ℤ) : ℤ) : ℝ) < d := by exact_mod_cast h3
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hdr]; nlinarith
  · rw [div_lt_iff₀ hdr]; nlinarith

/-- `s β(x)` as an integer: `t x − s ⌊(2 t x + s)/(2 s)⌋`. -/
def rr (s t : ℕ) (x : ℤ) : ℤ := t * x - s * ((2 * t * x + s) / (2 * s : ℕ))

theorem rr_beta (s t : ℕ) [NeZero s] (x : ℤ) : (rr s t x : ℝ) / s = beta s t x := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hs2 : 0 < 2 * s := by have := Nat.pos_of_ne_zero (NeZero.ne s); omega
  unfold beta frac nearest rr
  have hfl : ⌊(t : ℝ) * x / s + 1 / 2⌋ = (2 * t * x + s) / (2 * s : ℕ) := by
    rw [← floor_div_int _ _ hs2]
    congr 1
    push_cast
    field_simp
  rw [hfl]
  push_cast
  field_simp

/-- The off-diagonal weight table. -/
def tableE (s t α p : ℕ) (ℓ : ZMod s) (h : ℤ) : ℤ :=
  expPi true p (((α : ℤ) ^ 2 * ((t * h + rr s t ℓ.val) ^ 2 - (rr s t (ℓ.val + h)) ^ 2)).toNat) (s ^ 2)

theorem tableE_err (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hp : 13 ≤ p) (ℓ : ZMod s) (h : ℤ) :
    |(tableE s t α p ℓ h : ℝ) - 2 ^ p * exp (normExp s t (α : ℝ) ℓ.val h)| ≤ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hb : 0 < s ^ 2 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne s)) 2
  have hA := rr_beta s t (ℓ.val : ℤ)
  have hB := rr_beta s t ((ℓ.val : ℤ) + h)
  set A := rr s t ℓ.val
  set B := rr s t (ℓ.val + h)
  have hnn : 0 ≤ ((t : ℤ) * h + A) ^ 2 - B ^ 2 := by
    by_cases h0 : h = 0
    · subst h0
      simp [A, B]
    · have hge := NLogN.exponent_ge s t hst (beta s t ℓ.val) (beta s t (ℓ.val + h))
        (NLogN.abs_beta_le s t _) (NLogN.abs_beta_le s t _) h h0
      rw [← hA, ← hB] at hge
      have h1 : (0 : ℝ) ≤ 2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 := by
        have : (1 : ℝ) ≤ (t : ℝ) / s := by
          rw [le_div_iff₀ hs, one_mul]; exact_mod_cast hst.le
        positivity
      have h2 : (0 : ℝ) ≤ ((t : ℝ) * h / s + A / s) ^ 2 - (B / s) ^ 2 := le_trans h1 hge
      have e : ((t : ℝ) * h / s + A / s) ^ 2 - (B / s) ^ 2 = ((((t : ℤ) * h + A) ^ 2 - B ^ 2 : ℤ) : ℝ) / s ^ 2 := by
        push_cast; field_simp
      rw [e] at h2
      have : (0 : ℝ) ≤ ((((t : ℤ) * h + A) ^ 2 - B ^ 2 : ℤ) : ℝ) := by
        have := mul_nonneg h2 (by positivity : (0 : ℝ) ≤ (s : ℝ) ^ 2)
        rwa [div_mul_cancel₀ _ (by positivity)] at this
      exact_mod_cast this
  have ha : ((((α : ℤ) ^ 2 * (((t : ℤ) * h + A) ^ 2 - B ^ 2)).toNat : ℕ) : ℝ) =
      (α : ℝ) ^ 2 * (((t : ℝ) * h + A) ^ 2 - B ^ 2) := by
    rw [show ((((α : ℤ) ^ 2 * (((t : ℤ) * h + A) ^ 2 - B ^ 2)).toNat : ℕ) : ℝ) =
        ((((α : ℤ) ^ 2 * (((t : ℤ) * h + A) ^ 2 - B ^ 2)) : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (mul_nonneg (sq_nonneg (α : ℤ)) hnn)]
    push_cast; ring
  have hexp : normExp s t (α : ℝ) ℓ.val h = -(π * ((((α : ℤ) ^ 2 * (((t : ℤ) * h + A) ^ 2 - B ^ 2)).toNat : ℕ) : ℝ) /
      ((s ^ 2 : ℕ) : ℝ)) := by
    rw [ha]
    unfold normExp
    rw [← hA, ← hB]
    push_cast
    field_simp
    ring
  have hW := expPi_neg_err p (((α : ℤ) ^ 2 * (((t : ℤ) * h + A) ^ 2 - B ^ 2)).toNat) (s ^ 2) hp hb
  unfold tableE
  rw [hexp]
  linarith

/-- The diagonal weight table: `⌊expPi (π α² β²) / 2^(2α²)⌋`. -/
def tableD (s t α p : ℕ) (ℓ : ZMod s) : ℤ :=
  expPi false p (((α : ℤ) ^ 2 * (rr s t ℓ.val) ^ 2).toNat) (s ^ 2) / 2 ^ (2 * α ^ 2)

theorem tableD_spec (s t α p : ℕ) [NeZero s] [NeZero t] (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (ℓ : ZMod s) :
    |(tableD s t α p ℓ : ℝ) - 2 ^ p * dPrime s t (α : ℝ) ℓ| ≤ 2 ∧ 0 ≤ tableD s t α p ℓ ∧
      tableD s t α p ℓ ≤ 2 ^ p := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hb : 0 < s ^ 2 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne s)) 2
  have hA := rr_beta s t (ℓ.val : ℤ)
  set A := rr s t ℓ.val
  have ha : ((((α : ℤ) ^ 2 * A ^ 2).toNat : ℕ) : ℝ) = (α : ℝ) ^ 2 * (A : ℝ) ^ 2 := by
    rw [show ((((α : ℤ) ^ 2 * A ^ 2).toNat : ℕ) : ℝ) = ((((α : ℤ) ^ 2 * A ^ 2) : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (by positivity)]
    push_cast; ring
  set x : ℝ := π * ((((α : ℤ) ^ 2 * A ^ 2).toNat : ℕ) : ℝ) / ((s ^ 2 : ℕ) : ℝ) with hxdef
  have hxb : x = π * (α : ℝ) ^ 2 * beta s t ℓ.val ^ 2 := by
    rw [hxdef, ha, ← hA]; push_cast; field_simp
  have hβ := NLogN.abs_beta_le s t (ℓ.val : ℤ)
  have hβ2 : beta s t ℓ.val ^ 2 ≤ 1 / 4 := by
    have := sq_abs (beta s t ℓ.val); nlinarith [abs_nonneg (beta s t ℓ.val)]
  have hpi := pi_lt_d2
  have hpi3 := pi_gt_three
  have hαp' : (α : ℝ) ^ 2 ≤ p := by exact_mod_cast hαp
  have hx0 : 0 ≤ x := by rw [hxb]; positivity
  have hxle : x ≤ π * (α : ℝ) ^ 2 / 4 := by
    rw [hxb]
    have := mul_le_mul_of_nonneg_left hβ2 (by positivity : (0 : ℝ) ≤ π * (α : ℝ) ^ 2)
    linarith
  have hxp : x ≤ p - 1 := by
    have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hW := expPi_pos_err p (((α : ℤ) ^ 2 * A ^ 2).toNat) (s ^ 2) hp hb hxp
  rw [← hxdef] at hW
  set W := expPi false p (((α : ℤ) ^ 2 * A ^ 2).toNat) (s ^ 2)
  have hceil : ⌈(α : ℝ) ^ 2⌉₊ = α ^ 2 := by exact_mod_cast Nat.ceil_natCast (α ^ 2)
  have hd : dPrime s t (α : ℝ) ℓ = exp x / 2 ^ (2 * α ^ 2) := by
    unfold dPrime NLogN.dCoef
    rw [hceil, hxb]
  have h4 : (0 : ℝ) < 2 ^ (2 * α ^ 2) := by positivity
  have h4' : (4 : ℝ) ≤ 2 ^ (2 * α ^ 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * α ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hdiv := fdiv_err W (2 ^ (2 * α ^ 2)) (by positivity)
  rw [Int.cast_pow, Int.cast_ofNat] at hdiv
  have hex1 : 1 ≤ exp x := one_le_exp hx0
  have h2p : (8192 : ℝ) ≤ 2 ^ p := by
    calc (8192 : ℝ) = 2 ^ 13 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  refine ⟨?_, ?_, ?_⟩
  · unfold tableD
    rw [hd]
    have e : ((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) - 2 ^ p * (exp x / 2 ^ (2 * α ^ 2)) =
        (((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) - (W : ℝ) / 2 ^ (2 * α ^ 2)) + ((W : ℝ) - 2 ^ p * exp x) / 2 ^ (2 * α ^ 2) := by
      field_simp; ring
    rw [e]
    calc _ ≤ |((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) - (W : ℝ) / 2 ^ (2 * α ^ 2)| +
          |((W : ℝ) - 2 ^ p * exp x) / 2 ^ (2 * α ^ 2)| := abs_add_le _ _
      _ ≤ 1 + (3 / 2) / 4 := by
          refine add_le_add hdiv ?_
          rw [abs_div, abs_of_pos h4]
          calc |(W : ℝ) - 2 ^ p * exp x| / 2 ^ (2 * α ^ 2) ≤ (3 / 2) / 2 ^ (2 * α ^ 2) := by gcongr
            _ ≤ (3 / 2) / 4 := by gcongr
      _ ≤ 2 := by norm_num
  · unfold tableD
    have hW0 : (0 : ℝ) ≤ W := by
      have := (abs_le.mp hW).1
      nlinarith
    exact Int.ediv_nonneg (by exact_mod_cast hW0) (by positivity)
  · unfold tableD
    have hWle : (W : ℝ) ≤ 2 ^ p * exp x + 3 / 2 := by linarith [(abs_le.mp hW).2]
    have hexpx : exp x ≤ exp 1 ^ (α ^ 2) := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      push_cast
      nlinarith [sq_nonneg (α : ℝ)]
    have he1 := exp_one_lt_d9
    have hratio : exp 1 ^ (α ^ 2) / 2 ^ (2 * α ^ 2) ≤ 3 / 4 := by
      rw [pow_mul, ← div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      calc (exp 1 / 4) ^ (α ^ 2) ≤ (exp 1 / 4) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by norm_num)]; linarith)
              (by nlinarith)
        _ ≤ 3 / 4 := by rw [pow_one]; linarith
    have hq : ((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) ≤ 2 ^ p := by
      have h1 : ((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) ≤ (W : ℝ) / 2 ^ (2 * α ^ 2) := by
        have := (abs_le.mp hdiv).2
        have h0 : ((W / 2 ^ (2 * α ^ 2) : ℤ) : ℝ) * 2 ^ (2 * α ^ 2) ≤ W := by
          have : (W / 2 ^ (2 * α ^ 2)) * 2 ^ (2 * α ^ 2) ≤ W := Int.ediv_mul_le _ (by positivity)
          exact_mod_cast this
        rw [le_div_iff₀ h4]; exact h0
      calc _ ≤ (W : ℝ) / 2 ^ (2 * α ^ 2) := h1
        _ ≤ (2 ^ p * exp x + 3 / 2) / 2 ^ (2 * α ^ 2) := by gcongr
        _ = 2 ^ p * (exp x / 2 ^ (2 * α ^ 2)) + (3 / 2) / 2 ^ (2 * α ^ 2) := by ring
        _ ≤ 2 ^ p * (3 / 4) + (3 / 2) / 4 := by
            refine add_le_add (mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hexpx h4.le).trans hratio)
              (by positivity)) ?_
            gcongr
        _ ≤ 2 ^ p := by linarith
    exact_mod_cast hq

/-- Lemma 7.1 with the computed tables: for natural `α ≥ 2`, the tables
`tableA`, `tableE`, `tableD` satisfy the hypotheses of the tabled maps. -/
theorem tables_ok (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hp : 13 ≤ p) (hα : 2 ≤ α)
    (hαp : α ^ 2 ≤ p) :
    (∀ k j, |(tableA s t α p k j : ℝ) - 2 ^ p * resampWeight s t (α : ℝ) k j| ≤ 2) ∧
    (∀ ℓ h, |(tableE s t α p ℓ h : ℝ) - 2 ^ p * exp (normExp s t (α : ℝ) ℓ.val h)| ≤ 2) ∧
    (∀ ℓ, |(tableD s t α p ℓ : ℝ) - 2 ^ p * dPrime s t (α : ℝ) ℓ| ≤ 2) ∧
    (∀ ℓ, 0 ≤ tableD s t α p ℓ ∧ tableD s t α p ℓ ≤ 2 ^ p) :=
  ⟨fun k j => tableA_err s t α p hp hα k j, fun ℓ h => tableE_err s t α p hst hp ℓ h,
    fun ℓ => (tableD_spec s t α p hp (by omega) hαp ℓ).1,
    fun ℓ => (tableD_spec s t α p hp (by omega) hαp ℓ).2⟩

end Tables

end IntegerMultBounds.Resampling.WeightTable
