import IntegerMultBounds.NLogN.Multidim

/-! The `d`-dimensional discrete Fourier transform on `(i : Fin d) → ZMod (N i)`
with one primitive root per axis. Proved: the convolution theorem, character
orthogonality, double-transform inversion up to the factor `∏ N i`, and the
splitting of a `(d+1)`-dimensional transform into a one-dimensional transform
along the first axis applied to `d`-dimensional transforms of the slices. No
cost accounting or algorithm is part of this file. -/

namespace IntegerMultBounds.NLogN

variable {R : Type*} [CommRing R] {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The `d`-dimensional transform with root `ζ i` along axis `i`. -/
def dftD (ζ : Fin d → R) (a : ((i : Fin d) → ZMod (N i)) → R) :
    ((i : Fin d) → ZMod (N i)) → R :=
  fun k => ∑ j, (∏ i, ζ i ^ (j i * k i).val) * a j

theorem prod_pow_val_add {ζ : Fin d → R} (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i))
    (x y k : (i : Fin d) → ZMod (N i)) :
    (∏ i, ζ i ^ ((x + y) i * k i).val) =
      (∏ i, ζ i ^ (x i * k i).val) * ∏ i, ζ i ^ (y i * k i).val := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul, pow_val_add (hζ i)]

omit [∀ i, NeZero (N i)] in
theorem prod_pow_val_mul_comm (ζ : Fin d → R) (x y : (i : Fin d) → ZMod (N i)) :
    (∏ i, ζ i ^ (x i * y i).val) = ∏ i, ζ i ^ (y i * x i).val := by
  simp_rw [mul_comm]

/-- Convolution theorem in `d` dimensions. -/
theorem dftD_convG {ζ : Fin d → R} (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i))
    (a b : ((i : Fin d) → ZMod (N i)) → R) :
    dftD ζ (convG a b) = fun k => dftD ζ a k * dftD ζ b k := by
  funext k
  simp only [dftD, convG]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, prod_pow_val_add hζ]
  ring

/-- Orthogonality: the row sum is `∏ N i` on the trivial character and `0` otherwise. -/
theorem sum_prod_pow_val [IsDomain R] {ζ : Fin d → R}
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i)) (m : (i : Fin d) → ZMod (N i)) :
    ∑ j : (i : Fin d) → ZMod (N i), ∏ i, ζ i ^ (j i * m i).val =
      if m = 0 then (∏ i, (N i : R)) else 0 := by
  rw [← Fintype.prod_sum (fun i (j : ZMod (N i)) => ζ i ^ (j * m i).val)]
  simp_rw [sum_pow_val (hζ _)]
  rw [Fintype.prod_ite_zero]
  congr 1
  simp [funext_iff]

/-- Applying the transform twice gives `∏ N i` times the index-reflected vector. -/
theorem dftD_dftD [IsDomain R] {ζ : Fin d → R} (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i))
    (a : ((i : Fin d) → ZMod (N i)) → R) :
    dftD ζ (dftD ζ a) = fun k => (∏ i, (N i : R)) * a (-k) := by
  funext k
  simp only [dftD, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i j : (i : Fin d) → ZMod (N i),
      (∏ l, ζ l ^ (j l * k l).val) * ((∏ l, ζ l ^ (i l * j l).val) * a i) =
        a i * ∏ l, ζ l ^ (j l * (i + k) l).val := by
    intro i j
    rw [prod_pow_val_mul_comm ζ j (i + k), prod_pow_val_add hζ, prod_pow_val_mul_comm ζ i j,
      prod_pow_val_mul_comm ζ j k]
    ring
  simp_rw [h, ← Finset.mul_sum, sum_prod_pow_val hζ, add_eq_zero_iff_eq_neg, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

/-- A `(d+1)`-dimensional transform is a one-dimensional transform along the
first axis of the `d`-dimensional transforms of the slices. -/
theorem dftD_succ {N : Fin (d + 1) → ℕ} [∀ i, NeZero (N i)] (ζ : Fin (d + 1) → R)
    (a : ((i : Fin (d + 1)) → ZMod (N i)) → R) :
    dftD ζ a = fun k => dft (ζ 0)
      (fun j₀ => dftD (Fin.tail ζ) (fun j' => a (Fin.cons j₀ j')) (Fin.tail k)) (k 0) := by
  funext k
  simp only [dftD, dft, Finset.mul_sum]
  rw [← Equiv.sum_comp (Fin.consEquiv fun i => ZMod (N i)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail]
  ring

end IntegerMultBounds.NLogN
