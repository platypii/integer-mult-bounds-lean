import IntegerMultBounds.NLogN.ResamplingAssembly
import IntegerMultBounds.NLogN.TensorApproxD

/-! Theorem 4.1 of Harvey and van der Hoeven: the multidimensional resampling
factorization. Proved: the normalized transform `dftC` is the normalized `dft`
at the inverse root of unity; rectangular tensor products of operators between
coordinate spaces, defined through their matrix entries, compose factorwise,
scale by the product of the scalars, and have operator norm at most one when
every factor does; the normalized `d`-dimensional transform is the tensor of
the normalized one-dimensional transforms; and for coprime `s_i < t_i`,
`α ≥ 1`, and `α² θ_i ≥ 1`, the `d`-dimensional source transform equals
`2^(dγ) · B ∘ F_t ∘ A` with `‖A‖, ‖B‖ ≤ 1`. The numerical approximation of
`A` and `B` and every cost are not here. -/

open Real Complex

namespace IntegerMultBounds.NLogN

section Bridge

variable {n : ℕ} [NeZero n]

theorem chrZ_zero' : chrZ n 0 = 1 := by
  simp [chrZ, chr_zero]

theorem chrZ_neg' (m : ZMod n) : chrZ n (-m) = (chrZ n m)⁻¹ := by
  have h := chrZ_add n m (-m)
  rw [add_neg_cancel, chrZ_zero'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- `dftC` is the normalized `dft` at the inverse root of unity. -/
theorem dftC_eq_dftNormZ (u : ZMod n → ℂ) :
    dftC n u = dftNormZ n (Complex.exp (2 * π * I / n))⁻¹ u := by
  funext j
  unfold dftC dftNormZ dft
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [inv_pow, ← chrZ_eq_pow, ← chrZ_neg', mul_comm j k]

end Bridge

section Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix entry of an operator between coordinate spaces. -/
def matOf (A : (ι → ℂ) →L[ℂ] (κ → ℂ)) (k : κ) (j : ι) : ℂ := A (Pi.single j 1) k

theorem eq_sum_single (u : ι → ℂ) : u = ∑ j, u j • (Pi.single j 1 : ι → ℂ) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem clm_apply_eq_sum (A : (ι → ℂ) →L[ℂ] (κ → ℂ)) (u : ι → ℂ) (k : κ) :
    A u k = ∑ j, matOf A k j * u j := by
  conv_lhs => rw [eq_sum_single u]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [matOf]
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [Fintype ι] in
theorem matOf_comp {μ : Type*} [Fintype κ] [DecidableEq κ]
    (B : (κ → ℂ) →L[ℂ] (μ → ℂ)) (A : (ι → ℂ) →L[ℂ] (κ → ℂ)) (k : μ) (j : ι) :
    matOf (B ∘L A) k j = ∑ j', matOf B k j' * matOf A j' j := by
  show B (A (Pi.single j 1)) k = _
  rw [clm_apply_eq_sum]
  rfl

/-- Row sums of the matrix are bounded by the sup-norm operator norm. -/
theorem sum_norm_matOf_le [Fintype κ] (A : (ι → ℂ) →L[ℂ] (κ → ℂ)) (k : κ) :
    ∑ j, ‖matOf A k j‖ ≤ ‖A‖ := by
  classical
  let v : ι → ℂ := fun j =>
    if matOf A k j = 0 then 0 else (starRingEnd ℂ) (matOf A k j) / (‖matOf A k j‖ : ℂ)
  have hv : ‖v‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simp only [v]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr h)]
  have hA : A v k = ∑ j, (‖matOf A k j‖ : ℂ) := by
    rw [clm_apply_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [v]
    split_ifs with h
    · simp [h]
    · have hne : (‖matOf A k j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [mul_div_assoc', Complex.mul_conj', sq, mul_div_assoc, div_self hne, mul_one]
  calc ∑ j, ‖matOf A k j‖
      = ‖((∑ j, ‖matOf A k j‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    _ = ‖A v k‖ := by rw [hA]; push_cast; rfl
    _ ≤ ‖A v‖ := norm_le_pi_norm _ _
    _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := mul_one _

end Matrix

section Tensor

variable {d : ℕ} {M N : Fin d → ℕ} [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]

/-- The rectangular tensor product of `d` operators, through its matrix entries. -/
noncomputable def tensorRCLM (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) :
    (((i : Fin d) → ZMod (M i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    ∑ j, (∏ i, matOf (A i) (k i) (j i)) • ContinuousLinearMap.proj j

omit [∀ i, NeZero (N i)] in
theorem tensorRCLM_apply (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (u : ((i : Fin d) → ZMod (M i)) → ℂ) (k : (i : Fin d) → ZMod (N i)) :
    tensorRCLM A u k = ∑ j, (∏ i, matOf (A i) (k i) (j i)) * u j := by
  simp [tensorRCLM]

omit [∀ i, NeZero (N i)] in
theorem matOf_tensorRCLM (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (k : (i : Fin d) → ZMod (N i)) (j : (i : Fin d) → ZMod (M i)) :
    matOf (tensorRCLM A) k j = ∏ i, matOf (A i) (k i) (j i) := by
  show tensorRCLM A (Pi.single j 1) k = _
  rw [tensorRCLM_apply]
  simp [Pi.single_apply]

/-- Tensor products compose factorwise. -/
theorem tensorRCLM_comp {P : Fin d → ℕ} [∀ i, NeZero (P i)]
    (B : (i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (P i) → ℂ))
    (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) :
    tensorRCLM (fun i => B i ∘L A i) = tensorRCLM B ∘L tensorRCLM A := by
  ext u k
  rw [ContinuousLinearMap.comp_apply, tensorRCLM_apply, tensorRCLM_apply]
  simp_rw [tensorRCLM_apply, Finset.mul_sum, matOf_comp]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_sum (fun i j' => matOf (B i) (k i) j' * matOf (A i) j' (j i)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

omit [∀ i, NeZero (N i)] in
/-- Tensor products scale by the product of the scalars. -/
theorem tensorRCLM_smul (c : Fin d → ℂ)
    (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ)) :
    tensorRCLM (fun i => c i • A i) = (∏ i, c i) • tensorRCLM A := by
  ext u k
  change _ = (∏ i, c i) * tensorRCLM A u k
  rw [tensorRCLM_apply, tensorRCLM_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ i, matOf (c i • A i) (k i) (j i) = c i * matOf (A i) (k i) (j i) := fun i => rfl
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, mul_assoc]

/-- A tensor of contractions is a contraction. -/
theorem opNorm_tensorRCLM_le (A : (i : Fin d) → (ZMod (M i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (hA : ∀ i, ‖A i‖ ≤ 1) : ‖tensorRCLM A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  rw [tensorRCLM_apply]
  calc ‖∑ j, (∏ i, matOf (A i) (k i) (j i)) * u j‖
      ≤ ∑ j, ‖(∏ i, matOf (A i) (k i) (j i)) * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j : (i : Fin d) → ZMod (M i), (∏ i, ‖matOf (A i) (k i) (j i)‖) * ‖u‖ := by
        gcongr with j
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u j)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (∏ i, ∑ j', ‖matOf (A i) (k i) j'‖) * ‖u‖ := by
        rw [Fintype.prod_sum (fun i j' => ‖matOf (A i) (k i) j'‖), Finset.sum_mul]
    _ ≤ 1 * ‖u‖ := by
        gcongr
        exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          fun i _ => (sum_norm_matOf_le (A i) (k i)).trans (hA i)
    _ = ‖u‖ := one_mul _

end Tensor

section MultiDFT

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The normalized `d`-dimensional transform as an operator. -/
noncomputable def dftDCLM (N : Fin d → ℕ) [∀ i, NeZero (N i)] :
    (((i : Fin d) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k => ∑ j,
    ((1 / ((∏ i, N i : ℕ) : ℂ)) * ∏ i, chrZ (N i) (-(k i * j i))) • ContinuousLinearMap.proj j

theorem dftDCLM_apply (u : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftDCLM N u = fun k => (1 / ((∏ i, N i : ℕ) : ℂ)) *
      dftD (fun i => (Complex.exp (2 * π * I / (N i)))⁻¹) u k := by
  funext k
  simp only [dftDCLM, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  unfold dftD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_pow, ← chrZ_eq_pow, ← chrZ_neg', mul_comm (j i) (k i)]

theorem matOf_dftCLM {n : ℕ} [NeZero n] (k j : ZMod n) :
    matOf (dftCLM n) k j = (1 / (n : ℂ)) * chrZ n (-(k * j)) := by
  show dftCLM n (Pi.single j 1) k = _
  rw [dftCLM_apply]
  unfold dftC
  simp [Pi.single_apply]

/-- The normalized `d`-dimensional transform is the tensor of the normalized
one-dimensional transforms. -/
theorem dftDCLM_eq_tensor : dftDCLM N = tensorRCLM (fun i => dftCLM (N i)) := by
  ext u k
  rw [dftDCLM_apply, tensorRCLM_apply]
  dsimp only
  unfold dftD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  congr 1
  rw [Finset.prod_congr rfl fun i _ => matOf_dftCLM (k i) (j i), Finset.prod_mul_distrib]
  congr 1
  · simp only [one_div, Nat.cast_prod, Finset.prod_inv_distrib]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [inv_pow, ← chrZ_eq_pow, ← chrZ_neg', mul_comm (j i) (k i)]

end MultiDFT

section Factorization

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ}

/-- Theorem 4.1: the `d`-dimensional source transform factors through the
`d`-dimensional target transform with contractive outer maps. -/
theorem resampling_factorization_multi (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1)) :
    ∃ (A : (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ))
      (B : (((i : Fin d) → ZMod (t i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ)),
      dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) • (B ∘L dftDCLM t ∘L A) ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 := by
  have h := fun i => resampling_factorization (hst i) (hcop i) hα (hθ i)
  choose A B hAB hA hB using h
  refine ⟨tensorRCLM A, tensorRCLM B, ?_, opNorm_tensorRCLM_le A hA,
    opNorm_tensorRCLM_le B hB⟩
  rw [dftDCLM_eq_tensor, dftDCLM_eq_tensor]
  have e : (fun i => dftCLM (s i)) =
      fun i => ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) • (B i ∘L dftCLM (t i) ∘L A i) := funext hAB
  rw [e, tensorRCLM_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    mul_comm (2 * ⌈α ^ 2⌉₊ + 2) d, tensorRCLM_comp B (fun i => dftCLM (t i) ∘L A i),
    tensorRCLM_comp (fun i => dftCLM (t i)) A]

end Factorization

end IntegerMultBounds.NLogN
