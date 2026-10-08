import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! The discrete Fourier transform over an integral domain with a primitive
`N`-th root of unity, indexed by `ZMod N`. Proved: linearity, the cyclic
convolution theorem, the orthogonality sum, double-transform inversion up to
the factor `N`, injectivity when `N` is a nonzero scalar, and uniqueness of the
convolution with a given pointwise-product transform. No fast evaluation
algorithm, cost model, or rounding analysis is part of this file. -/

namespace IntegerMultBounds.NLogN

variable {R : Type*} [CommRing R] {N : ℕ} [NeZero N] {ζ : R}

/-- Forward transform `a ↦ (k ↦ ∑ⱼ ζ^{jk} aⱼ)`, exponents reduced in `ZMod N`. -/
def dft (ζ : R) (a : ZMod N → R) : ZMod N → R :=
  fun k => ∑ j, ζ ^ (j * k).val * a j

/-- Cyclic convolution `(a ⊛ b)ₖ = ∑ᵢ aᵢ b_{k-i}`. -/
def cconv (a b : ZMod N → R) : ZMod N → R :=
  fun k => ∑ i, a i * b (k - i)

omit [NeZero N] in
theorem pow_val_natCast (hζ : IsPrimitiveRoot ζ N) (n : ℕ) :
    ζ ^ ((n : ZMod N)).val = ζ ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem pow_val_add (hζ : IsPrimitiveRoot ζ N) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  have h : x + y = ((x.val + y.val : ℕ) : ZMod N) := by push_cast; simp
  rw [h, pow_val_natCast hζ, pow_add]

theorem pow_val_mul (hζ : IsPrimitiveRoot ζ N) (x y : ZMod N) :
    ζ ^ (x * y).val = (ζ ^ x.val) ^ y.val := by
  have h : x * y = ((x.val * y.val : ℕ) : ZMod N) := by push_cast; simp
  rw [h, pow_val_natCast hζ, pow_mul]

theorem cconv_comm (a b : ZMod N → R) : cconv a b = cconv b a := by
  funext k
  simp only [cconv]
  exact Fintype.sum_equiv (Equiv.subLeft k) _ _ fun i => by
    simp [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

theorem dft_add (ζ : R) (a b : ZMod N → R) : dft ζ (a + b) = dft ζ a + dft ζ b := by
  funext k
  simp [dft, mul_add, Finset.sum_add_distrib]

theorem dft_smul (ζ : R) (c : R) (a : ZMod N → R) : dft ζ (c • a) = c • dft ζ a := by
  funext k
  simp [dft, Finset.mul_sum, mul_left_comm]

/-- The transform of a cyclic convolution is the pointwise product of transforms. -/
theorem dft_cconv (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N → R) :
    dft ζ (cconv a b) = fun k => dft ζ a k * dft ζ b k := by
  funext k
  simp only [dft, cconv]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, add_mul, pow_val_add hζ]
  ring

theorem sum_range_pow_val (f : ℕ → R) :
    ∑ j : ZMod N, f j.val = ∑ n ∈ Finset.range N, f n := by
  refine Finset.sum_nbij' (fun j => j.val) (fun n => (n : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.2 (ZMod.val_lt j)
  · intro n _
    exact Finset.mem_univ _
  · intro j _
    exact ZMod.natCast_zmod_val j
  · intro n hn
    exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hn)
  · intro j _
    rfl

/-- Orthogonality of characters: the row sum is `N` on the trivial character and `0` otherwise. -/
theorem sum_pow_val [IsDomain R] (hζ : IsPrimitiveRoot ζ N) (m : ZMod N) :
    ∑ j : ZMod N, ζ ^ (j * m).val = if m = 0 then (N : R) else 0 := by
  have h : ∀ j : ZMod N, ζ ^ (j * m).val = (ζ ^ m.val) ^ j.val := by
    intro j
    rw [mul_comm, pow_val_mul hζ]
  simp_rw [h]
  rw [sum_range_pow_val (fun n => (ζ ^ m.val) ^ n)]
  split_ifs with hm
  · subst hm
    simp
  · have hx : ζ ^ m.val ≠ 1 := by
      intro h1
      rw [hζ.pow_eq_one_iff_dvd] at h1
      have := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt m)
      exact hm ((ZMod.val_eq_zero m).1 this)
    have hN : (ζ ^ m.val) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hmul := geom_sum_mul (ζ ^ m.val) N
    rw [hN, sub_self, mul_eq_zero] at hmul
    exact hmul.resolve_right (sub_ne_zero.2 hx)

/-- Applying the transform twice gives `N` times the index-reflected vector. -/
theorem dft_dft [IsDomain R] (hζ : IsPrimitiveRoot ζ N) (a : ZMod N → R) :
    dft ζ (dft ζ a) = fun k => (N : R) * a (-k) := by
  funext k
  simp only [dft, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i j : ZMod N,
      ζ ^ (j * k).val * (ζ ^ (i * j).val * a i) = a i * ζ ^ (j * (i + k)).val := by
    intro i j
    rw [mul_add, pow_val_add hζ, mul_comm i j]
    ring
  simp_rw [h, ← Finset.mul_sum, sum_pow_val hζ, add_eq_zero_iff_eq_neg, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

theorem dft_injective [IsDomain R] (hζ : IsPrimitiveRoot ζ N) (hN : (N : R) ≠ 0)
    {u v : ZMod N → R} (h : dft ζ u = dft ζ v) : u = v := by
  funext k
  have h2 := congrFun (congrArg (dft ζ) h) (-k)
  rw [dft_dft hζ, dft_dft hζ] at h2
  simp only [neg_neg] at h2
  exact mul_left_cancel₀ hN h2

/-- Any vector whose transform is the pointwise product of transforms is the convolution. -/
theorem eq_cconv_of_dft_eq [IsDomain R] (hζ : IsPrimitiveRoot ζ N) (hN : (N : R) ≠ 0)
    {a b c : ZMod N → R} (hc : dft ζ c = fun k => dft ζ a k * dft ζ b k) :
    c = cconv a b :=
  dft_injective hζ hN (hc.trans (dft_cconv hζ a b).symm)

end IntegerMultBounds.NLogN
