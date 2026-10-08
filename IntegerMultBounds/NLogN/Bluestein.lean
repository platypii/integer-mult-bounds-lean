import IntegerMultBounds.NLogN.MultidimD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Bluestein's chirp identity. For an even length `t` the transform with root
`e^{-2πi/t}` is a pointwise multiplication by the conjugate chirp, a cyclic
convolution with the chirp, and another conjugate-chirp multiplication. The
`d`-dimensional version on a product of even-length cyclic groups is also
proved. This reduces transforms to convolutions; no cost model, rounding, or
synthetic-ring realization of the convolution is part of this file. -/

namespace IntegerMultBounds.NLogN

open Complex Real

variable {t : ℕ} [NeZero t]

/-- `e^{π i x / t}` for an integer `x`. -/
noncomputable def chirpExp (t : ℕ) (x : ℤ) : ℂ := Complex.exp (π * I * x / t)

theorem chirpExp_add_mul (x m : ℤ) : chirpExp t (x + 2 * t * m) = chirpExp t x := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  unfold chirpExp
  have : π * I * ((x + 2 * t * m : ℤ) : ℂ) / t = π * I * x / t + m * (2 * π * I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem chirpExp_sq_add (ht : 2 ∣ t) (x q : ℤ) :
    chirpExp t ((x + t * q) ^ 2) = chirpExp t (x ^ 2) := by
  obtain ⟨s, hs⟩ := ht
  have h : (x + t * q) ^ 2 = x ^ 2 + 2 * t * (q * x + s * q ^ 2) := by
    rw [show (t : ℤ) = 2 * s by exact_mod_cast hs]
    ring
  rw [h, chirpExp_add_mul]

omit [NeZero t] in
theorem chirpExp_conj (x : ℤ) : (starRingEnd ℂ) (chirpExp t x) = chirpExp t (-x) := by
  unfold chirpExp
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_natCast]
  push_cast
  ring

omit [NeZero t] in
theorem chirpExp_mul (x y : ℤ) : chirpExp t x * chirpExp t y = chirpExp t (x + y) := by
  unfold chirpExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The chirp `a_j = e^{π i j² / t}`, equation (3.1) of the paper. -/
noncomputable def chirp (t : ℕ) (j : ZMod t) : ℂ :=
  Complex.exp (π * I * (j.val ^ 2 : ℕ) / t)

omit [NeZero t] in
theorem chirp_eq (j : ZMod t) : chirp t j = chirpExp t ((j.val : ℤ) ^ 2) := by
  unfold chirp chirpExp
  push_cast
  rfl

omit [NeZero t] in
/-- Two naturals with the same residue differ by a multiple of `t`. -/
theorem exists_int_of_cast_eq {a b : ℕ} (h : (a : ZMod t) = b) :
    ∃ q : ℤ, (a : ℤ) = b + t * q := by
  have h0 : (((a : ℤ) - b : ℤ) : ZMod t) = 0 := by
    push_cast
    rw [h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  obtain ⟨q, hq⟩ := h0
  exact ⟨q, by linarith⟩

theorem val_sub_eq (j k : ZMod t) : ∃ q : ℤ, ((j - k).val : ℤ) = j.val - k.val + t * q := by
  have h0 : ((((j - k).val : ℤ) - (j.val - k.val) : ℤ) : ZMod t) = 0 := by
    push_cast
    simp only [ZMod.natCast_zmod_val, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  obtain ⟨q, hq⟩ := h0
  exact ⟨q, by linarith⟩

/-- `a_{j-k} ā_j ā_k = e^{-2π i jk/t}` for even `t`: the identity `-2jk = (j-k)² - j² - k²`. -/
theorem chirp_sub_mul (ht : 2 ∣ t) (j k : ZMod t) :
    chirp t (j - k) * (starRingEnd ℂ) (chirp t j) * (starRingEnd ℂ) (chirp t k) =
      Complex.exp (-2 * π * I * (j.val * k.val : ℕ) / t) := by
  obtain ⟨q, hq⟩ := val_sub_eq j k
  rw [chirp_eq, chirp_eq, chirp_eq, chirpExp_conj, chirpExp_conj, hq, chirpExp_sq_add ht,
    chirpExp_mul, chirpExp_mul]
  unfold chirpExp
  congr 1
  push_cast
  ring

omit [NeZero t] in
theorem exp_neg_two_eq (n : ℕ) : Complex.exp (-2 * π * I * n / t) = chirpExp t (-2 * n) := by
  unfold chirpExp
  congr 1
  push_cast
  ring

theorem exp_congr_of_cast_eq {a b : ℕ} (h : (a : ZMod t) = b) :
    Complex.exp (-2 * π * I * a / t) = Complex.exp (-2 * π * I * b / t) := by
  obtain ⟨q, hq⟩ := exists_int_of_cast_eq h
  rw [exp_neg_two_eq, exp_neg_two_eq, hq,
    show -2 * ((b : ℤ) + t * q) = -2 * b + 2 * t * (-q) by ring, chirpExp_add_mul]

/-- The root `e^{-2πi/t}` raised to a reduced product exponent. -/
theorem omega_pow_val (j k : ZMod t) :
    Complex.exp (-2 * π * I / t) ^ (j * k).val =
      Complex.exp (-2 * π * I * (j.val * k.val : ℕ) / t) := by
  rw [← Complex.exp_nat_mul]
  have h : Complex.exp (((j * k).val : ℕ) * (-2 * π * I / t)) =
      Complex.exp (-2 * π * I * ((j * k).val : ℕ) / t) := by
    congr 1
    ring
  rw [h]
  apply exp_congr_of_cast_eq
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem convG_comm {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] [Fintype G]
    (a b : G → R) : convG a b = convG b a := by
  funext k
  simp only [convG]
  exact Fintype.sum_equiv (Equiv.subLeft k) _ _ fun i => by
    simp [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

/-- Bluestein, one dimension: `F u = ā · (a ∗ (ā · u))` for even `t` (no `1/t` factor). -/
theorem bluestein (ht : 2 ∣ t) (u : ZMod t → ℂ) :
    dft (Complex.exp (-2 * π * I / t)) u =
      fun k => (starRingEnd ℂ) (chirp t k) *
        cconv (chirp t) (fun j => (starRingEnd ℂ) (chirp t j) * u j) k := by
  funext k
  rw [cconv_comm]
  simp only [dft, cconv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [omega_pow_val]
  have h := chirp_sub_mul ht k j
  rw [mul_comm k.val j.val] at h
  rw [← h]
  ring

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The multidimensional chirp `a_{j₁,…,j_d} = ∏ᵢ e^{π i jᵢ²/tᵢ}`. -/
noncomputable def chirpD (N : Fin d → ℕ) (j : (i : Fin d) → ZMod (N i)) : ℂ :=
  ∏ i, chirp (N i) (j i)

/-- Bluestein in `d` dimensions, all lengths even. -/
theorem bluesteinD (hN : ∀ i, 2 ∣ N i) (u : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftD (fun i => Complex.exp (-2 * π * I / (N i))) u =
      fun k => (starRingEnd ℂ) (chirpD N k) *
        convG (chirpD N) (fun j => (starRingEnd ℂ) (chirpD N j) * u j) k := by
  funext k
  rw [convG_comm]
  simp only [dftD, convG, Finset.mul_sum, chirpD, map_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ i, Complex.exp (-2 * π * I / (N i)) ^ (j i * k i).val =
      chirp (N i) ((k - j) i) * (starRingEnd ℂ) (chirp (N i) (k i)) *
        (starRingEnd ℂ) (chirp (N i) (j i)) := fun i => by
    rw [omega_pow_val, Pi.sub_apply, chirp_sub_mul (hN i), mul_comm (k i).val]
  simp only [h, Finset.prod_mul_distrib]
  ring

end IntegerMultBounds.NLogN
