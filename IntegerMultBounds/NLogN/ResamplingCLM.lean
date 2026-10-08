import IntegerMultBounds.NLogN.ResamplingNorm
import IntegerMultBounds.NLogN.Neumann
import IntegerMultBounds.NLogN.Approx

/-! The resampling ingredients of Harvey–van der Hoeven, Section 4.1, packaged
as continuous linear maps on `ZMod n → ℂ` with the sup norm. Proved: the
normalised transform, the two index permutations, and both Gaussian resampling
maps are continuous linear maps agreeing with the pointwise definitions; the
transform and permutations have operator norm at most one; `P_s` is invertible
for coprime lengths with inverse of norm at most one; `S` has operator norm at
most `1 + 1/α`; the resampling identity holds as an equation of continuous
linear maps; and every vector has a fixed-point approximation with scaled
error at most two. The square subsystem, its inverse, and costs are not here. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap Real Complex

/-! ### Precomposition and the sup norm -/

theorem norm_comp_le_pi_norm {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ)
    (x : κ → ℂ) : ‖x ∘ f‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm x (f i)

/-! ### The normalised transform -/

section DFT

variable {n : ℕ} [NeZero n]

/-- `dftC n` as a continuous linear map. -/
noncomputable def dftCLM (n : ℕ) [NeZero n] : (ZMod n → ℂ) →L[ℂ] (ZMod n → ℂ) :=
  pi fun j => ∑ k, ((1 / n : ℂ) * chrZ n (-(j * k))) • proj k

theorem dftCLM_apply (u : ZMod n → ℂ) : dftCLM n u = dftC n u := by
  funext j
  simp [dftCLM, dftC, Finset.mul_sum, mul_assoc]

/-- Each entry of the normalised transform is bounded by the sup norm (Example 2.6). -/
theorem norm_dftC_le_pi (u : ZMod n → ℂ) (j : ZMod n) : ‖dftC n u j‖ ≤ ‖u‖ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold dftC
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc 1 / (n : ℝ) * ‖∑ k, chrZ n (-(j * k)) * u k‖
      ≤ 1 / (n : ℝ) * ∑ k, ‖chrZ n (-(j * k)) * u k‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ 1 / (n : ℝ) * ∑ _k : ZMod n, ‖u‖ := by
        gcongr with k
        rw [norm_mul, chrZ, norm_chr, one_mul]
        exact norm_le_pi_norm u k
    _ = ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp

theorem opNorm_dftCLM_le : ‖dftCLM n‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity), one_mul, dftCLM_apply]
  intro j
  exact norm_dftC_le_pi u j

end DFT

/-! ### The index permutations -/

section Perm

variable {s t : ℕ}

/-- `permS t` as a continuous linear map. -/
noncomputable def permSCLM (t : ℕ) : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  pi fun j => proj (t * j)

theorem permSCLM_apply (u : ZMod s → ℂ) : permSCLM t u = permS t u := by
  funext j
  simp [permSCLM, permS]

theorem opNorm_permSCLM_le [NeZero s] : ‖(permSCLM t : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, permSCLM_apply]
  exact norm_comp_le_pi_norm (fun j : ZMod s => (t : ZMod s) * j) u

/-- `permT s` as a continuous linear map. -/
noncomputable def permTCLM (s : ℕ) : (ZMod t → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  pi fun k => proj (-(s * k))

theorem permTCLM_apply (u : ZMod t → ℂ) : permTCLM s u = permT s u := by
  funext k
  simp [permTCLM, permT]

theorem opNorm_permTCLM_le [NeZero t] : ‖(permTCLM s : (ZMod t → ℂ) →L[ℂ] (ZMod t → ℂ))‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, permTCLM_apply]
  exact norm_comp_le_pi_norm (fun k : ZMod t => -((s : ZMod t) * k)) u

/-- For coprime lengths, multiplication by `t` is a bijection of `ZMod s`. -/
noncomputable def mulTEquiv (hst : Nat.Coprime s t) : ZMod s ≃ ZMod s :=
  Units.mulLeft (ZMod.unitOfCoprime t hst.symm)

theorem mulTEquiv_apply (hst : Nat.Coprime s t) (j : ZMod s) :
    mulTEquiv hst j = (t : ZMod s) * j := by
  simp [mulTEquiv, ZMod.coe_unitOfCoprime]

/-- `permS t` as a continuous linear equivalence, for coprime `s` and `t`. -/
noncomputable def permSEquiv (hst : Nat.Coprime s t) : (ZMod s → ℂ) ≃L[ℂ] (ZMod s → ℂ) where
  toLinearEquiv := LinearEquiv.funCongrLeft ℂ ℂ (mulTEquiv hst)
  continuous_toFun := by
    refine continuous_pi fun j => ?_
    exact continuous_apply _
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    exact continuous_apply _

theorem permSEquiv_apply (hst : Nat.Coprime s t) (u : ZMod s → ℂ) :
    permSEquiv hst u = permS t u := by
  funext j
  change u (mulTEquiv hst j) = u (t * j)
  rw [mulTEquiv_apply]

theorem permSEquiv_symm_apply (hst : Nat.Coprime s t) (u : ZMod s → ℂ) :
    (permSEquiv hst).symm u = u ∘ (mulTEquiv hst).symm := rfl

theorem permSEquiv_coe (hst : Nat.Coprime s t) :
    (permSEquiv hst : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) = permSCLM t := by
  ext u j
  change permSEquiv hst u j = permSCLM t u j
  rw [permSEquiv_apply, permSCLM_apply]

theorem opNorm_permSEquiv_symm_le [NeZero s] (hst : Nat.Coprime s t) :
    ‖((permSEquiv hst).symm : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul]
  change ‖(permSEquiv hst).symm u‖ ≤ ‖u‖
  rw [permSEquiv_symm_apply]
  exact norm_comp_le_pi_norm _ u

end Perm

/-! ### The resampling maps -/

section Resamp

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The Gaussian weight of `S` at output `k` and integer input index `j`. -/
noncomputable def weightS (s t : ℕ) [NeZero t] (α : ℝ) (k : ZMod t) (j : ℤ) : ℝ :=
  Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2)

/-- The Gaussian weight of `T` at output `k` and integer input index `j`. -/
noncomputable def weightT (s t : ℕ) [NeZero t] (α : ℝ) (k : ZMod t) (j : ℤ) : ℝ :=
  Real.exp (-π * α ^ 2 * t ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2)

/-- The finite matrix entry of `S`: the sum of the weights over one residue class. -/
noncomputable def coefS (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (k : ZMod t) (m : ZMod s) : ℂ :=
  ∑' q : ℤ, (weightS s t α k (q * s + m.val) : ℂ)

/-- The finite matrix entry of `T`. -/
noncomputable def coefT (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (k : ZMod t) (m : ZMod s) : ℂ :=
  ∑' q : ℤ, (weightT s t α k (q * s + m.val) : ℂ)

/-- The series defining `resampT` converges absolutely. -/
theorem summable_resampT_term (hα : 0 < α) (u : ZMod s → ℂ) (ℓ : ZMod t) :
    Summable (fun j : ℤ =>
      (Real.exp (-π * α ^ 2 * t ^ 2 * ((ℓ.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have hc : 0 < π * α ^ 2 * t ^ 2 / s ^ 2 := by positivity
  refine Summable.of_norm_bounded
    (g := fun j : ℤ => gauss (π * α ^ 2 * t ^ 2 / s ^ 2) (-(s * ℓ.val / t) + j) * ∑ k, ‖u k‖)
    ((summable_gauss_int hc _).mul_right _) (fun j => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-π * α ^ 2 * t ^ 2 * ((ℓ.val : ℝ) / t - j / s) ^ 2) =
      gauss (π * α ^ 2 * t ^ 2 / s ^ 2) (-(s * ℓ.val / t) + j) := by
    unfold gauss
    congr 1
    field_simp
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_le_sum_norm u _) (gauss_pos _ _).le

theorem cast_residue (m : ZMod s) (q : ℤ) : (((q * s + m.val : ℤ) : ZMod s)) = m := by
  push_cast
  simp

/-- `S` as a finite sum over residue classes. -/
theorem resampS_eq_finite (hα : 0 < α) (u : ZMod s → ℂ) (k : ZMod t) :
    resampS s t α u k = (1 / α : ℂ) * ∑ m : ZMod s, coefS s t α k m * u m := by
  unfold resampS
  congr 1
  rw [tsum_regroup s _ (summable_resampS_term hα u k)]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold coefS weightS
  rw [← tsum_mul_right]
  refine tsum_congr fun q => ?_
  rw [cast_residue]

/-- `T` as a finite sum over residue classes. -/
theorem resampT_eq_finite (hα : 0 < α) (u : ZMod s → ℂ) (k : ZMod t) :
    resampT s t α u k = ∑ m : ZMod s, coefT s t α k m * u m := by
  unfold resampT
  rw [tsum_regroup s _ (summable_resampT_term hα u k)]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold coefT weightT
  rw [← tsum_mul_right]
  refine tsum_congr fun q => ?_
  rw [cast_residue]

/-- `resampS s t α` as a continuous linear map. -/
noncomputable def resampSCLM (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  pi fun k => ∑ m, ((1 / α : ℂ) * coefS s t α k m) • proj m

/-- `resampT s t α` as a continuous linear map. -/
noncomputable def resampTCLM (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  pi fun k => ∑ m, coefT s t α k m • proj m

theorem resampSCLM_apply (hα : 0 < α) (u : ZMod s → ℂ) :
    resampSCLM s t α u = resampS s t α u := by
  funext k
  rw [resampS_eq_finite hα]
  simp [resampSCLM, Finset.mul_sum, mul_assoc]

theorem resampTCLM_apply (hα : 0 < α) (u : ZMod s → ℂ) :
    resampTCLM s t α u = resampT s t α u := by
  funext k
  rw [resampT_eq_finite hα]
  simp [resampTCLM]

/-- Lemma 4.5 as an operator-norm bound. -/
theorem opNorm_resampSCLM_le (hα : 0 < α) : ‖resampSCLM s t α‖ ≤ 1 + 1 / α := by
  refine opNorm_le_of_unit_norm (by positivity) fun u hu => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity), resampSCLM_apply hα]
  intro k
  refine norm_resampS_le hα u (fun j => ?_) k
  rw [← hu]
  exact norm_le_pi_norm u j

/-- Theorem 4.2 as an equation of continuous linear maps. -/
theorem resampling_identity_clm (hα : 0 < α) :
    resampTCLM s t α ∘L permSCLM t ∘L dftCLM s =
      permTCLM s ∘L dftCLM t ∘L resampSCLM s t α := by
  ext u k
  simp only [comp_apply]
  rw [dftCLM_apply, permSCLM_apply, resampTCLM_apply hα, resampSCLM_apply hα, dftCLM_apply,
    permTCLM_apply]
  exact congrFun (resampling_identity hα u) k

end Resamp

/-! ### Fixed-point approximation of vectors -/

/-- Rounding every entry gives a `p`-bit approximation with scaled error at most two. -/
theorem exists_fixed_approx {n : ℕ} (p : ℕ) (a : ZMod n → ℂ) :
    ∃ a' : ZMod n → ℂ, (∀ j, (2 : ℝ) ^ p * ‖a' j - a j‖ ≤ 2) ∧ (∀ j, ‖a' j‖ ≤ ‖a j‖) := by
  refine ⟨fun j => rhoC p (a j), fun j => ?_, fun j => norm_rhoC_le p (a j)⟩
  have h := norm_rhoC_sub_le_two p (a j)
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  calc (2 : ℝ) ^ p * ‖rhoC p (a j) - a j‖ ≤ 2 ^ p * (2 / 2 ^ p) := by gcongr
    _ = 2 := by field_simp

end IntegerMultBounds.NLogN
