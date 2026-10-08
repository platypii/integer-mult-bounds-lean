import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic

/-! Analytic preliminaries for Gaussian resampling. Proved: the Gaussian
`exp (-α x²)` is positive, at most one, and decreasing in `|x|`; its integer
translates are summable with an explicit geometric tail bound; the periodised
Gaussian `θ_α(x) = ∑_{m ∈ ℤ} exp (-α (x + m)²)` is positive, invariant under
integer shifts, bounded below by `exp (-α/4)` and above by an explicit constant
depending only on `α`; and the Gaussian Poisson summation identity restated for
`gauss`. The resampling matrix, its inverse, and any error analysis of the
resampled transform are not part of this file. -/

namespace IntegerMultBounds.NLogN

open Real

noncomputable def gauss (α x : ℝ) : ℝ := Real.exp (-α * x ^ 2)

variable {α : ℝ}

theorem gauss_pos (α x : ℝ) : 0 < gauss α x := Real.exp_pos _

theorem gauss_le_one (hα : 0 ≤ α) (x : ℝ) : gauss α x ≤ 1 := by
  unfold gauss
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg x]

theorem gauss_antitone_abs (hα : 0 ≤ α) {x y : ℝ} (h : |x| ≤ |y|) :
    gauss α y ≤ gauss α x := by
  unfold gauss
  rw [Real.exp_le_exp]
  have : x ^ 2 ≤ y ^ 2 := sq_le_sq.mpr h
  nlinarith

/-- Comparison of a Gaussian value with a geometric term, the engine of every
summability and tail statement below. -/
theorem gauss_le_exp_mul (hα : 0 < α) (x : ℝ) (n : ℕ) {y : ℝ}
    (hy : (n : ℝ) ^ 2 / 2 - x ^ 2 ≤ y ^ 2) :
    gauss α y ≤ Real.exp (α * x ^ 2) * Real.exp ((n : ℝ) * (-α / 2)) := by
  unfold gauss
  rw [← Real.exp_add, Real.exp_le_exp]
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have := Nat.le_self_pow two_ne_zero n
    exact_mod_cast this
  have h1 := mul_le_mul_of_nonneg_left hy hα.le
  have h2 := mul_le_mul_of_nonneg_left hn hα.le
  nlinarith

theorem summable_gauss_of_le (hα : 0 < α) (x : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, (n : ℝ) ^ 2 / 2 - x ^ 2 ≤ f n ^ 2) :
    Summable (fun n : ℕ => gauss α (f n)) := by
  have hs : Summable (fun n : ℕ => Real.exp (α * x ^ 2) * Real.exp ((n : ℝ) * (-α / 2))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _
  exact hs.of_nonneg_of_le (fun n => (gauss_pos _ _).le) (fun n => gauss_le_exp_mul hα x n (hf n))

theorem summable_gauss_int (hα : 0 < α) (x : ℝ) :
    Summable (fun m : ℤ => gauss α (x + m)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simp only [Int.cast_natCast]
    exact summable_gauss_of_le hα x (fun n => x + n) (fun n => by nlinarith [sq_nonneg (2 * x + n)])
  · simp only [Int.cast_neg, Int.cast_natCast]
    exact summable_gauss_of_le hα x (fun n => x + -(n : ℝ))
      (fun n => by nlinarith [sq_nonneg (2 * x - n)])

theorem summable_gauss_nat (hα : 0 < α) (c : ℝ) :
    Summable (fun n : ℕ => gauss α (c + n)) := by
  have := (summable_int_iff_summable_nat_and_neg.mp (summable_gauss_int hα c)).1
  simpa only [Int.cast_natCast] using this

/-- Geometric tail bound for the one-sided Gaussian sum beyond `K`. -/
theorem gauss_tail_le (hα : 0 < α) (K : ℕ) :
    ∑' m : ℕ, gauss α ((K : ℝ) + 1 + m) ≤
      gauss α ((K : ℝ) + 1) / (1 - Real.exp (-α * (2 * K + 3))) := by
  set r := Real.exp (-α * (2 * K + 3)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hterm : ∀ m : ℕ, gauss α ((K : ℝ) + 1 + m) ≤ gauss α ((K : ℝ) + 1) * r ^ m := by
    intro m
    unfold gauss
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      have := Nat.le_self_pow two_ne_zero m
      exact_mod_cast this
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_le_mul_of_nonneg_left hm hα.le, mul_nonneg hα.le (mul_nonneg hK (Nat.cast_nonneg m))]
  have hsum : Summable (fun m : ℕ => gauss α ((K : ℝ) + 1 + m)) := summable_gauss_nat hα _
  have hgeom : Summable (fun m : ℕ => gauss α ((K : ℝ) + 1) * r ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  calc ∑' m : ℕ, gauss α ((K : ℝ) + 1 + m)
      ≤ ∑' m : ℕ, gauss α ((K : ℝ) + 1) * r ^ m := hsum.tsum_le_tsum hterm hgeom
    _ = gauss α ((K : ℝ) + 1) * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = gauss α ((K : ℝ) + 1) / (1 - r) := by rw [div_eq_mul_inv]

/-- The full one-sided sum, bounded by a constant depending only on `α`. -/
theorem tsum_gauss_nat_le (hα : 0 < α) :
    ∑' n : ℕ, gauss α n ≤ 1 + 1 / (1 - Real.exp (-α * 3)) := by
  have hs' : Summable (fun n : ℕ => (fun n : ℕ => gauss α n) (n + 1)) := by
    refine (summable_gauss_nat hα 1).congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_comm]
  rw [tsum_eq_zero_add' (f := fun n : ℕ => gauss α n) hs']
  have h0 : gauss α ((0 : ℕ) : ℝ) = 1 := by simp [gauss]
  have htail := gauss_tail_le hα 0
  simp only [Nat.cast_zero, zero_add, mul_zero] at htail
  have hconv : (∑' n : ℕ, gauss α (((n + 1 : ℕ) : ℝ))) = ∑' m : ℕ, gauss α (1 + m) := by
    refine tsum_congr fun n => ?_
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_comm]
  have hr1 : Real.exp (-α * 3) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hpos : 0 < 1 - Real.exp (-α * 3) := by linarith
  have h1 : gauss α 1 / (1 - Real.exp (-α * 3)) ≤ 1 / (1 - Real.exp (-α * 3)) :=
    div_le_div_of_nonneg_right (gauss_le_one hα.le 1) hpos.le
  rw [h0, hconv]
  linarith

/-- The periodised Gaussian. -/
noncomputable def theta (α x : ℝ) : ℝ := ∑' m : ℤ, gauss α (x + m)

theorem theta_pos (hα : 0 < α) (x : ℝ) : 0 < theta α x :=
  (summable_gauss_int hα x).tsum_pos (fun _ => (gauss_pos _ _).le) 0 (gauss_pos _ _)

theorem theta_add_int (α x : ℝ) (k : ℤ) : theta α (x + k) = theta α x := by
  unfold theta
  rw [← (Equiv.addRight k).tsum_eq (fun m : ℤ => gauss α (x + m))]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring_nf

theorem theta_add_one (α x : ℝ) : theta α (x + 1) = theta α x := by
  simpa using theta_add_int α x 1

/-- Some translate of `x` lies within `1/2` of the origin, so `θ` is bounded
below by the Gaussian at `1/2`. -/
theorem gauss_half_le_theta (hα : 0 < α) (x : ℝ) : gauss α (1 / 2) ≤ theta α x := by
  have hsum := summable_gauss_int hα x
  have hle : gauss α (x + ((-round x : ℤ) : ℝ)) ≤ theta α x :=
    hsum.le_tsum (-round x) (fun _ _ => (gauss_pos _ _).le)
  refine le_trans ?_ hle
  apply gauss_antitone_abs hα.le
  have := abs_sub_round x
  rw [Int.cast_neg, ← sub_eq_add_neg]
  calc |x - round x| ≤ 1 / 2 := this
    _ = |(1 : ℝ) / 2| := by norm_num

/-- For `x ∈ [0, 1]` each half of the periodised sum is dominated termwise by
the sum over the naturals. -/
theorem theta_le_two_tsum (hα : 0 < α) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    theta α x ≤ 2 * ∑' n : ℕ, gauss α n := by
  have h1 : Summable (fun n : ℕ => gauss α (x + ((n : ℤ) : ℝ))) := by
    simpa only [Int.cast_natCast] using summable_gauss_nat hα x
  have h2 : Summable (fun n : ℕ => gauss α (x + ((-((n : ℤ) + 1) : ℤ) : ℝ))) := by
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    exact summable_gauss_of_le hα x (fun n => x + -((n : ℝ) + 1))
      (fun n => by nlinarith [sq_nonneg (2 * x - n - 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hs : Summable (fun n : ℕ => gauss α n) := by
    simpa only [zero_add] using summable_gauss_nat hα 0
  have hA : ∑' n : ℕ, gauss α (x + ((n : ℤ) : ℝ)) ≤ ∑' n : ℕ, gauss α n := by
    refine h1.tsum_le_tsum (fun n => ?_) hs
    apply gauss_antitone_abs hα.le
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n),
      abs_of_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
    linarith
  have hB : ∑' n : ℕ, gauss α (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ≤ ∑' n : ℕ, gauss α n := by
    refine h2.tsum_le_tsum (fun n => ?_) hs
    apply gauss_antitone_abs hα.le
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (Nat.cast_nonneg n), abs_of_nonpos (by linarith)]
    linarith
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => gauss α (x + m)) h1 h2
  unfold theta
  rw [hsplit]
  linarith

/-- A uniform explicit upper bound on the periodised Gaussian. -/
theorem theta_le (hα : 0 < α) (x : ℝ) :
    theta α x ≤ 2 * (1 + 1 / (1 - Real.exp (-α * 3))) := by
  have hx : theta α x = theta α (Int.fract x) := by
    conv_lhs => rw [← Int.floor_add_fract x, add_comm]
    exact theta_add_int α _ _
  rw [hx]
  calc theta α (Int.fract x)
      ≤ 2 * ∑' n : ℕ, gauss α n :=
        theta_le_two_tsum hα (Int.fract_nonneg x) (Int.fract_lt_one x).le
    _ ≤ 2 * (1 + 1 / (1 - Real.exp (-α * 3))) := by
        have := tsum_gauss_nat_le hα
        linarith

/-- Poisson summation for the Gaussian at the origin, restated for `gauss`. -/
theorem tsum_gauss_poisson {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, gauss (π * a) n) = 1 / a ^ (1 / 2 : ℝ) * ∑' n : ℤ, gauss (π / a) n := by
  simpa only [gauss, neg_mul, neg_div] using Real.tsum_exp_neg_mul_int_sq ha

end IntegerMultBounds.NLogN
