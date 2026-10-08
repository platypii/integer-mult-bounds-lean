import IntegerMultBounds.NLogN.FFT
import IntegerMultBounds.NLogN.FixedPoint
import IntegerMultBounds.NLogN.Kronecker

/-! The exact-arithmetic complex-FFT integer multiplier on `Fin (2 ^ n)`.
Proved: the cyclic convolution theorem and double-transform inversion for the
`Fin`-indexed transform, hence that forward transforms, a pointwise product,
an inverse transform, and division by `2 ^ n` compute the cyclic convolution;
with integer inputs the result is the integer convolution; and for digit lists
whose acyclic product fits in `2 ^ n` positions, rounding the real parts and
evaluating in any base gives the product of the two digit values. Arithmetic
here is exact over `ℂ`; no precision, cost, or tape compilation is involved. -/

namespace IntegerMultBounds.NLogN

open Complex

variable {R : Type*} [CommRing R]

/-- Cyclic convolution on `Fin N`, using the group subtraction of `Fin N`. -/
def cconvFin {N : ℕ} [NeZero N] (a b : Fin N → R) : Fin N → R :=
  fun k => ∑ i, a i * b (k - i)

theorem pow_val_mul_fin {N : ℕ} {ω : R} (hω : ω ^ N = 1) (x y : ℕ) :
    ω ^ (x % N * y) = ω ^ (x * y) := by
  rw [pow_mod_eq hω, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_mod_eq hω]

/-- The convolution theorem on `Fin N`. -/
theorem dftFin_cconvFin {N : ℕ} [NeZero N] {ω : R} (hω : ω ^ N = 1)
    (a b : Fin N → R) :
    dftFin ω (cconvFin a b) = fun k => dftFin ω a k * dftFin ω b k := by
  funext k
  simp only [dftFin, cconvFin]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.sum_equiv (Equiv.addLeft i)
    (fun m => ω ^ ((i + m).val * k.val) * (a i * b (i + m - i)))
    (fun j => ω ^ (j.val * k.val) * (a i * b (j - i))) (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro m _
  rw [add_sub_cancel_left, Fin.val_add, pow_val_mul_fin hω, add_mul, pow_add]
  ring

open scoped Classical in
/-- Geometric sum over `Fin N` of an `N`-th root of unity in a domain. -/
theorem geom_sum_fin {S : Type*} [CommRing S] [IsDomain S] {N : ℕ} {x : S}
    (hx : x ^ N = 1) : ∑ j : Fin N, x ^ j.val = if x = 1 then (N : S) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => x ^ j) N]
  split_ifs with h
  · simp [h]
  · have := geom_sum_mul x N
    rw [hx, sub_self, mul_eq_zero] at this
    rcases this with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') h

theorem orthogonality_fin {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (i k : Fin N) :
    ∑ j : Fin N, (ω ^ i.val * ω⁻¹ ^ k.val) ^ j.val = if i = k then (N : ℂ) else 0 := by
  have hx : (ω ^ i.val * ω⁻¹ ^ k.val) ^ N = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i.val, mul_comm k.val, pow_mul, pow_mul,
      hω.pow_eq_one, inv_pow, hω.pow_eq_one, inv_one, one_pow, one_pow, mul_one]
  rw [geom_sum_fin hx]
  have hne : ω ^ k.val ≠ 0 := pow_ne_zero _ (hω.ne_zero (NeZero.ne N))
  have hiff : ω ^ i.val * ω⁻¹ ^ k.val = 1 ↔ i = k := by
    rw [inv_pow, mul_inv_eq_one₀ hne]
    constructor
    · intro h; exact Fin.ext (hω.pow_inj i.isLt k.isLt h)
    · rintro rfl; rfl
  by_cases h : i = k
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

/-- Double transform with `ω` then `ω⁻¹` is multiplication by `N`. -/
theorem dftFin_dftFin_inv {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (a : Fin N → ℂ) : dftFin ω⁻¹ (dftFin ω a) = fun k => (N : ℂ) * a k := by
  funext k
  simp only [dftFin, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ i : Fin N, ∑ j : Fin N, ω⁻¹ ^ (j.val * k.val) * (ω ^ (i.val * j.val) * a i)
      = a i * ∑ j : Fin N, (ω ^ i.val * ω⁻¹ ^ k.val) ^ j.val := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k.val j.val]
    ring
  simp only [hterm, orthogonality_fin hω, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- Forward transforms, pointwise product, inverse transform, divide by `2 ^ n`. -/
noncomputable def fftMul (n : ℕ) (ω : ℂ) (a b : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  fun k => fft n ω⁻¹ (fun j => fft n ω a j * fft n ω b j) k / (2 ^ n : ℂ)

theorem fftMul_eq_cconvFin {n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ n))
    (a b : Fin (2 ^ n) → ℂ) : fftMul n ω a b = cconvFin a b := by
  have h1 : ω ^ (2 ^ n) = 1 := hω.pow_eq_one
  have h2 : ω⁻¹ ^ (2 ^ n) = 1 := by rw [inv_pow, h1, inv_one]
  funext k
  simp only [fftMul, fft_eq_dftFin n ω h1, fft_eq_dftFin n ω⁻¹ h2]
  have hc : (fun j => dftFin ω a j * dftFin ω b j) = dftFin ω (cconvFin a b) := by
    rw [dftFin_cconvFin h1]
  rw [hc, dftFin_dftFin_inv hω]
  push_cast
  exact mul_div_cancel_left₀ _ (pow_ne_zero n two_ne_zero)

/-- With integer inputs the output is the integer cyclic convolution. -/
theorem fftMul_int {n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ n))
    (A B : Fin (2 ^ n) → ℤ) :
    fftMul n ω (fun j => (A j : ℂ)) (fun j => (B j : ℂ)) =
      fun k => ((∑ i, A i * B (k - i) : ℤ) : ℂ) := by
  rw [fftMul_eq_cconvFin hω]
  funext k
  simp only [cconvFin]
  push_cast
  rfl

/-- The `Fin` convolution of zero-padded digit lists is the list-level one. -/
theorem cconvFin_eq_cconvList {N : ℕ} [NeZero N] (a b : List ℕ) (k : Fin N) :
    cconvFin (fun i : Fin N => (a.getD i 0 : ℂ)) (fun i => (b.getD i 0 : ℂ)) k =
      ((cconvList N a b).getD k 0 : ℂ) := by
  have hR : (cconvList N a b).getD k 0 =
      ∑ i ∈ Finset.range N, a.getD i 0 * b.getD ((k.val + N - i) % N) 0 := by
    simp [cconvList, List.getD_eq_getElem?_getD]
  rw [hR]
  push_cast
  simp only [cconvFin]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (a.getD i 0 : ℂ) * (b.getD ((k.val + N - i) % N) 0 : ℂ)) N]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.val_sub, show N - i.val + k.val = k.val + N - i.val by have := i.isLt; omega]

theorem aconv_length_le (a b : List ℕ) (hb : b ≠ []) :
    (aconv a b).length ≤ a.length + b.length - 1 := by
  cases a with
  | nil => simp
  | cons x xs => rw [aconv_length _ _ (List.cons_ne_nil x xs) hb]

/-- The cyclic convolution of sufficient length evaluates to the product. -/
theorem evalBase_cconvList (B : ℕ) {L : ℕ} {a b : List ℕ}
    (hL : a.length + b.length ≤ L + 1) :
    evalBase B (cconvList L a b) = evalBase B a * evalBase B b := by
  by_cases hb : b = []
  · subst hb
    have : cconvList L a [] = List.replicate L 0 := by
      simp only [cconvList, List.getD_nil, mul_zero, Finset.sum_const_zero]
      rw [List.map_const', List.length_range]
    rw [this, evalBase_replicate_zero]
    simp [evalBase]
  · have hlen : (aconv a b).length ≤ L := by
      have := aconv_length_le a b hb
      have hb' : 0 < b.length := List.length_pos_of_ne_nil hb
      omega
    rw [cconv_eq_pad hL hlen, evalBase_append_replicate, evalBase_aconv]

/-- Rounding the exact multiplier's outputs gives digits evaluating to the
product of the digit values, in every base. -/
theorem fftMul_product {n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ n))
    (B : ℕ) {a b : List ℕ} (hL : a.length + b.length ≤ 2 ^ n + 1) :
    evalBase B ((List.ofFn fun k : Fin (2 ^ n) =>
      round (fftMul n ω (fun i => (a.getD i 0 : ℂ)) (fun i => (b.getD i 0 : ℂ)) k).re).map
        Int.toNat) = evalBase B a * evalBase B b := by
  have hlist : (List.ofFn fun k : Fin (2 ^ n) =>
      round (fftMul n ω (fun i => (a.getD i 0 : ℂ)) (fun i => (b.getD i 0 : ℂ)) k).re).map
        Int.toNat = cconvList (2 ^ n) a b := by
    have hf : (fun k : Fin (2 ^ n) =>
        round (fftMul n ω (fun i => (a.getD i 0 : ℂ)) (fun i => (b.getD i 0 : ℂ)) k).re) =
        fun k : Fin (2 ^ n) => (((cconvList (2 ^ n) a b).getD k 0 : ℕ) : ℤ) := by
      funext k
      rw [fftMul_eq_cconvFin hω, cconvFin_eq_cconvList, natCast_re, round_natCast]
    rw [hf, List.map_ofFn]
    apply List.ext_getElem
    · simp
    · intro m h₁ h₂
      rw [List.getElem_ofFn]
      simp only [Function.comp, Int.toNat_natCast]
      rw [← getD_eq_getElem h₂]
  rw [hlist, evalBase_cconvList B hL]

end IntegerMultBounds.NLogN
