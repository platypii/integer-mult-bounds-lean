import IntegerMultBounds.NLogN.Approx

/-! The elementary fixed-point operations of Harvey and van der Hoeven,
Sections 2.3 to 2.5, at the level of error bounds. Proved: `p`-bit fixed-point
numbers are closed under rounding, sums, negation, and integer scaling; the
rounded half-sum of two fixed-point approximations errs by at most one unit
beyond half the input errors (Lemma 2.1); scaling a fixed-point approximation
by a natural number `c` needs no rounding and multiplies the error by `c`
(the exact-representation case of Lemma 2.2; the paper's adjustment back into
the unit ball is not modelled); the rounded product bound (Lemma 2.4); and,
for the synthetic ring represented by coefficient vectors, the negacyclic
product is commutative with `‖ab‖ ≤ r ‖a‖ ‖b‖` (Lemma 2.5) and multiplication
by a power of `y` is a signed cyclic shift of norm one. The bit costs
`O(p^{1+δ})` are not formalised, and the coefficient-vector product is not yet
identified with multiplication in `SynthRing`. -/

open Complex

namespace IntegerMultBounds.NLogN

/-- `u` is a `p`-bit fixed-point complex number. -/
def IsFixed (p : ℕ) (u : ℂ) : Prop := ∃ a b : ℤ, u = ⟨a / 2 ^ p, b / 2 ^ p⟩

theorem isFixed_rhoC (p : ℕ) (u : ℂ) : IsFixed p (rhoC p u) :=
  ⟨rho0 (2 ^ p * u.re), rho0 (2 ^ p * u.im), rfl⟩

theorem IsFixed.add {p : ℕ} {u v : ℂ} (hu : IsFixed p u) (hv : IsFixed p v) :
    IsFixed p (u + v) := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  refine ⟨a + c, b + d, ?_⟩
  apply Complex.ext <;> simp <;> ring

theorem IsFixed.neg {p : ℕ} {u : ℂ} (hu : IsFixed p u) : IsFixed p (-u) := by
  obtain ⟨a, b, rfl⟩ := hu
  refine ⟨-a, -b, ?_⟩
  apply Complex.ext <;> simp <;> ring

theorem IsFixed.sub {p : ℕ} {u v : ℂ} (hu : IsFixed p u) (hv : IsFixed p v) :
    IsFixed p (u - v) := by
  rw [sub_eq_add_neg]; exact hu.add hv.neg

theorem IsFixed.intMul {p : ℕ} {u : ℂ} (c : ℤ) (hu : IsFixed p u) :
    IsFixed p ((c : ℂ) * u) := by
  obtain ⟨a, b, rfl⟩ := hu
  refine ⟨c * a, c * b, ?_⟩
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem IsFixed.natMul {p : ℕ} {u : ℂ} (c : ℕ) (hu : IsFixed p u) :
    IsFixed p ((c : ℂ) * u) := by
  have := hu.intMul c
  simpa using this

theorem rho0_intCast (n : ℤ) : rho0 n = n := by
  unfold rho0
  split_ifs <;> simp

/-- Rounding a fixed-point number changes nothing. -/
theorem rhoC_of_isFixed {p : ℕ} {u : ℂ} (hu : IsFixed p u) : rhoC p u = u := by
  obtain ⟨a, b, rfl⟩ := hu
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  apply Complex.ext
  · rw [rhoC_re]
    simp only
    rw [mul_div_cancel₀ _ hp, rho0_intCast]
  · rw [rhoC_im]
    simp only
    rw [mul_div_cancel₀ _ hp, rho0_intCast]

/-- Rounding a half-integer toward zero moves it by at most one half. -/
theorem abs_rho0_half_sub (n : ℤ) : |(rho0 ((n : ℝ) / 2) : ℝ) - n / 2| ≤ 1 / 2 := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · subst hk
    have : ((2 * k : ℤ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
    rw [this, rho0_intCast, sub_self, abs_zero]
    norm_num
  · subst hk
    have hx : ((2 * k + 1 : ℤ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
    rw [hx]
    unfold rho0
    split_ifs with h
    · have : ⌊(k : ℝ) + 1 / 2⌋ = k := by
        rw [Int.floor_eq_iff]; constructor <;> linarith
      rw [this]
      rw [abs_le]; constructor <;> linarith
    · have : ⌈(k : ℝ) + 1 / 2⌉ = k + 1 := by
        rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      rw [this]; push_cast
      rw [abs_le]; constructor <;> linarith

/-- The rounded half-sum of two fixed-point numbers moves by at most `2^{-p}`. -/
theorem norm_rhoC_half_add_sub {p : ℕ} {u v : ℂ} (hu : IsFixed p u) (hv : IsFixed p v) :
    ‖rhoC p ((u + v) / 2) - (u + v) / 2‖ ≤ 1 / 2 ^ p := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set w : ℂ := (⟨a / 2 ^ p, b / 2 ^ p⟩ + ⟨c / 2 ^ p, d / 2 ^ p⟩) / 2 with hw
  have hre : 2 ^ p * w.re = ((a + c : ℤ) : ℝ) / 2 := by
    simp [hw]; field_simp
  have him : 2 ^ p * w.im = ((b + d : ℤ) : ℝ) / 2 := by
    simp [hw]; field_simp
  have h1 : |(rhoC p w - w).re| ≤ (1 / 2) / 2 ^ p := by
    rw [Complex.sub_re, rhoC_re]
    have e : (rho0 (2 ^ p * w.re) : ℝ) / 2 ^ p - w.re
        = ((rho0 (2 ^ p * w.re) : ℝ) - 2 ^ p * w.re) / 2 ^ p := by field_simp
    rw [e, abs_div, abs_of_pos hp, hre]
    exact div_le_div_of_nonneg_right (abs_rho0_half_sub _) hp.le
  have h2 : |(rhoC p w - w).im| ≤ (1 / 2) / 2 ^ p := by
    rw [Complex.sub_im, rhoC_im]
    have e : (rho0 (2 ^ p * w.im) : ℝ) / 2 ^ p - w.im
        = ((rho0 (2 ^ p * w.im) : ℝ) - 2 ^ p * w.im) / 2 ^ p := by field_simp
    rw [e, abs_div, abs_of_pos hp, him]
    exact div_le_div_of_nonneg_right (abs_rho0_half_sub _) hp.le
  calc ‖rhoC p w - w‖ ≤ |(rhoC p w - w).re| + |(rhoC p w - w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (1 / 2) / 2 ^ p + (1 / 2) / 2 ^ p := add_le_add h1 h2
    _ = 1 / 2 ^ p := by ring

/-- Lemma 2.1 (addition): the rounded half-sum errs by at most one unit beyond half the
input errors. -/
theorem approx_half_add {p : ℕ} {u v u₀ v₀ : ℂ} {η₁ η₂ : ℝ}
    (hu : IsFixed p u) (hv : IsFixed p v)
    (huu : 2 ^ p * ‖u - u₀‖ ≤ η₁) (hvv : 2 ^ p * ‖v - v₀‖ ≤ η₂) :
    2 ^ p * ‖rhoC p ((u + v) / 2) - (u₀ + v₀) / 2‖ ≤ (η₁ + η₂) / 2 + 1 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := norm_rhoC_half_add_sub hu hv
  have h2 : ‖(u + v) / 2 - (u₀ + v₀) / 2‖ ≤ (‖u - u₀‖ + ‖v - v₀‖) / 2 := by
    have e : (u + v) / 2 - (u₀ + v₀) / 2 = ((u - u₀) + (v - v₀)) / 2 := by ring
    rw [e, norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have h3 := norm_sub_le_norm_sub_add_norm_sub (rhoC p ((u + v) / 2)) ((u + v) / 2)
    ((u₀ + v₀) / 2)
  calc 2 ^ p * ‖rhoC p ((u + v) / 2) - (u₀ + v₀) / 2‖
      ≤ 2 ^ p * (1 / 2 ^ p + (‖u - u₀‖ + ‖v - v₀‖) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hp.le
    _ = 1 + (2 ^ p * ‖u - u₀‖ + 2 ^ p * ‖v - v₀‖) / 2 := by field_simp
    _ ≤ (η₁ + η₂) / 2 + 1 := by linarith

/-- Lemma 2.1 (subtraction). -/
theorem approx_half_sub {p : ℕ} {u v u₀ v₀ : ℂ} {η₁ η₂ : ℝ}
    (hu : IsFixed p u) (hv : IsFixed p v)
    (huu : 2 ^ p * ‖u - u₀‖ ≤ η₁) (hvv : 2 ^ p * ‖v - v₀‖ ≤ η₂) :
    2 ^ p * ‖rhoC p ((u - v) / 2) - (u₀ - v₀) / 2‖ ≤ (η₁ + η₂) / 2 + 1 := by
  have h := approx_half_add hu hv.neg huu (η₂ := η₂) (v₀ := -v₀) (by rwa [neg_sub_neg, norm_sub_rev])
  simpa [sub_eq_add_neg] using h

/-- Lemma 2.2 in the exact case: a natural scaling of a fixed-point number is again
fixed-point, so rounding is the identity and the error scales by `c`. -/
theorem approx_scale {p : ℕ} {u u₀ : ℂ} {η : ℝ} (c : ℕ) (hu : IsFixed p u)
    (huu : 2 ^ p * ‖u - u₀‖ ≤ η) :
    2 ^ p * ‖rhoC p ((c : ℂ) * u) - (c : ℂ) * u₀‖ ≤ c * η := by
  rw [rhoC_of_isFixed (hu.natMul c), ← mul_sub, norm_mul, Complex.norm_natCast]
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc 2 ^ p * ((c : ℝ) * ‖u - u₀‖) = c * (2 ^ p * ‖u - u₀‖) := by ring
    _ ≤ c * η := by gcongr

/-- Lemma 2.4: the rounded product of unit-ball fixed-point approximations errs by at most
`2` beyond the input errors. This is `approx_mul_round`; fixed-point-ness is irrelevant. -/
theorem approx_mul_fixed {p : ℕ} {η₁ η₂ : ℝ} {u' u v' v : ℂ}
    (hu' : ‖u'‖ ≤ 1) (hv' : ‖v'‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (huu : 2 ^ p * ‖u' - u‖ ≤ η₁) (hvv : 2 ^ p * ‖v' - v‖ ≤ η₂) :
    2 ^ p * ‖rhoC p (u' * v') - u * v‖ ≤ 2 + η₁ + η₂ :=
  approx_mul_round hu' hv' hu huu hvv

section Negacyclic

variable {r : ℕ}

/-- The index paired with `i` in coefficient `k` of a negacyclic product: `k - i` modulo `r`.
It is an involution. -/
def negaIdx (k i : Fin r) : Fin r := k - i

/-- The sign attached to the pair `(i, k - i)`: negative exactly when the index wraps. -/
def negaSign (k i : Fin r) : ℂ := if i ≤ k then 1 else -1

theorem negaIdx_negaIdx [NeZero r] (k i : Fin r) : negaIdx k (negaIdx k i) = i := by
  unfold negaIdx; exact sub_sub_cancel k i

theorem negaIdx_le_iff (k i : Fin r) : negaIdx k i ≤ k ↔ i ≤ k := by
  unfold negaIdx
  have hi := i.isLt
  have hk := k.isLt
  constructor
  · intro h
    by_contra hik
    have hlt : k < i := lt_of_not_ge hik
    have := Fin.coe_sub_iff_lt.mpr hlt
    rw [Fin.le_def] at h
    omega
  · intro h
    have := Fin.coe_sub_iff_le.mpr h
    rw [Fin.le_def]
    omega

theorem negaSign_negaIdx (k i : Fin r) : negaSign k (negaIdx k i) = negaSign k i := by
  simp only [negaSign, negaIdx_le_iff]

theorem norm_negaSign (k i : Fin r) : ‖negaSign k i‖ = 1 := by
  unfold negaSign; split_ifs <;> simp

/-- The involution `i ↦ k - i` as a permutation of `Fin r`. -/
def negaPerm [NeZero r] (k : Fin r) : Equiv.Perm (Fin r) :=
  Function.Involutive.toPerm (negaIdx k) (negaIdx_negaIdx k)

/-- Multiplication of coefficient vectors modulo `y^r = -1`. -/
def negacyclicMul (a b : Fin r → ℂ) : Fin r → ℂ :=
  fun k => ∑ i, negaSign k i * a i * b (negaIdx k i)

theorem negacyclicMul_comm [NeZero r] (a b : Fin r → ℂ) : negacyclicMul a b = negacyclicMul b a := by
  funext k
  unfold negacyclicMul
  refine Fintype.sum_equiv (negaPerm k) (fun i => negaSign k i * a i * b (negaIdx k i))
    (fun i => negaSign k i * b i * a (negaIdx k i)) (fun i => ?_)
  show negaSign k i * a i * b (negaIdx k i)
    = negaSign k (negaIdx k i) * b (negaIdx k i) * a (negaIdx k (negaIdx k i))
  rw [negaSign_negaIdx, negaIdx_negaIdx]
  ring

/-- Lemma 2.5: the negacyclic product is bounded by `r ‖a‖ ‖b‖` in the sup norm. -/
theorem norm_negacyclicMul_le (a b : Fin r → ℂ) :
    ‖negacyclicMul a b‖ ≤ r * ‖a‖ * ‖b‖ := by
  have hab : (0 : ℝ) ≤ r * ‖a‖ * ‖b‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hab]
  intro k
  unfold negacyclicMul
  calc ‖∑ i, negaSign k i * a i * b (negaIdx k i)‖
      ≤ ∑ i, ‖negaSign k i * a i * b (negaIdx k i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin r, ‖a‖ * ‖b‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_mul, norm_negaSign, one_mul]
        exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b _) (norm_nonneg _)
          (norm_nonneg _)
    _ = r * ‖a‖ * ‖b‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Multiplication by `y^k`: a cyclic shift by `k` with a sign on the wrapped coefficients. -/
def shiftNeg (k : Fin r) (a : Fin r → ℂ) : Fin r → ℂ :=
  fun i => negaSign i k * a (i - k)

theorem norm_shiftNeg_le (k : Fin r) (a : Fin r → ℂ) : ‖shiftNeg k a‖ ≤ ‖a‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  unfold shiftNeg
  rw [norm_mul, norm_negaSign, one_mul]
  exact norm_le_pi_norm a _

/-- The shift is the negacyclic product with the monomial `y^k`. -/
theorem shiftNeg_eq_negacyclicMul (k : Fin r) (a : Fin r → ℂ) :
    shiftNeg k a = negacyclicMul (Pi.single k 1) a := by
  funext i
  unfold negacyclicMul shiftNeg negaIdx
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

end Negacyclic

end IntegerMultBounds.NLogN
