import IntegerMultBounds.NLogN.ResamplingInverse
import IntegerMultBounds.NLogN.ResamplingCLM

/-! Proposition 4.7(i) of Harvey–van der Hoeven in one dimension. The row
selection `C`, the diagonal map `D` with its inverse, and the off-diagonal part
`E = C T D - 1` are packaged as continuous linear maps on `ZMod n → ℂ`, with
`‖C‖ ≤ 1`, `‖D‖ ≤ e^{π α² / 4} ≤ 2^{2⌈α²⌉}`, and `‖E‖ ≤ 1/2` under `α² θ ≥ 1`.
Proved: for `s < t` coprime and `α ≥ 1`, there are `A : ℂ^s → ℂ^t` and
`B : ℂ^t → ℂ^s` with `‖A‖, ‖B‖ ≤ 1` and `F_s = 2^γ B F_t A`, `γ = 2⌈α²⌉ + 2`;
and the explicit shapes `A = S/2`, `B = P_s⁻¹ D J C P_t / 2^{γ-1}` for any left
inverse `J` of `1 + E`. Numerical approximation of `A` and `B`, the
multidimensional version, and costs are not here. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap Real

/-! ### Explicit assembly, generic -/

section Explicit

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A left inverse of `1 + E` with `‖E‖ ≤ 1/2` has norm at most two. -/
theorem norm_left_inverse_le (E J : U →L[ℂ] U) (hE : ‖E‖ ≤ 1 / 2)
    (hJ : J ∘L (1 + E) = 1) : ‖J‖ ≤ 2 := by
  have h : J = 1 - J ∘L E := by
    have h' : J ∘L (1 + E) = J + J ∘L E := by ext x; simp
    rw [h'] at hJ
    rw [← hJ]; abel
  have h1 : ‖(1 : U →L[ℂ] U)‖ ≤ 1 := by rw [one_def]; exact norm_id_le
  have : ‖J‖ ≤ 1 + ‖J‖ * (1 / 2) := by
    calc ‖J‖ = ‖1 - J ∘L E‖ := by rw [← h]
      _ ≤ ‖(1 : U →L[ℂ] U)‖ + ‖J ∘L E‖ := norm_sub_le _ _
      _ ≤ 1 + ‖J‖ * ‖E‖ := by gcongr; exact opNorm_comp_le _ _
      _ ≤ 1 + ‖J‖ * (1 / 2) := by gcongr
  linarith

/-- `assemble` with the inverse `J` and the maps `A = S`, `B = P_s⁻¹ D J C P_t` explicit. -/
theorem assemble_explicit (Fs : U →L[ℂ] U) (Ft : W →L[ℂ] W) (S T : U →L[ℂ] W)
    (Ps : U ≃L[ℂ] U) (Pt : W →L[ℂ] W) (C : W →L[ℂ] U) (D D' E J : U →L[ℂ] U)
    (hres : T ∘L (Ps : U →L[ℂ] U) ∘L Fs = Pt ∘L Ft ∘L S)
    (hN : C ∘L T ∘L D = 1 + E) (hJ : J ∘L (1 + E) = 1) (hD : D ∘L D' = 1) :
    Fs = ((Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt) ∘L Ft ∘L S := by
  ext x
  have h1 : Pt (Ft (S x)) = T (Ps (Fs x)) := by
    have := congrArg (fun f => f x) hres
    simpa using this.symm
  have h2 : D (D' (Ps (Fs x))) = Ps (Fs x) := by
    have := congrArg (fun f => f (Ps (Fs x))) hD
    simpa using this
  have h3 : C (T (D (D' (Ps (Fs x))))) = (1 + E) (D' (Ps (Fs x))) := by
    have := congrArg (fun f => f (D' (Ps (Fs x)))) hN
    simpa using this
  have h4 : J ((1 + E) (D' (Ps (Fs x)))) = D' (Ps (Fs x)) := by
    have := congrArg (fun f => f (D' (Ps (Fs x)))) hJ
    simpa using this
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe]
  calc Fs x = Ps.symm (Ps (Fs x)) := (Ps.symm_apply_apply _).symm
    _ = Ps.symm (D (D' (Ps (Fs x)))) := by rw [h2]
    _ = Ps.symm (D (J ((1 + E) (D' (Ps (Fs x)))))) := by rw [h4]
    _ = Ps.symm (D (J (C (T (D (D' (Ps (Fs x)))))))) := by rw [h3]
    _ = Ps.symm (D (J (C (T (Ps (Fs x)))))) := by rw [h2]
    _ = Ps.symm (D (J (C (Pt (Ft (S x)))))) := by rw [h1]

/-- The scaled normal form with explicit maps `A' = S / 2` and
`B' = P_s⁻¹ D J C P_t / 2^{γ₁ + 1}`. -/
theorem normal_form_explicit (Fs : U →L[ℂ] U) (Ft : W →L[ℂ] W) (S T : U →L[ℂ] W)
    (Ps : U ≃L[ℂ] U) (Pt : W →L[ℂ] W) (C : W →L[ℂ] U) (D D' E J : U →L[ℂ] U) (γ₁ : ℕ)
    (hres : T ∘L (Ps : U →L[ℂ] U) ∘L Fs = Pt ∘L Ft ∘L S)
    (hN : C ∘L T ∘L D = 1 + E) (hE : ‖E‖ ≤ 1 / 2) (hJ : J ∘L (1 + E) = 1)
    (hD : D ∘L D' = 1) (hS : ‖S‖ ≤ 2) (hDn : ‖D‖ ≤ 2 ^ γ₁)
    (hPs : ‖(Ps.symm : U →L[ℂ] U)‖ ≤ 1) (hC : ‖C‖ ≤ 1) (hPt : ‖Pt‖ ≤ 1) :
    Fs = ((2 : ℂ) ^ (γ₁ + 2)) •
      ((((2 : ℂ) ^ (γ₁ + 1))⁻¹ • ((Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt)) ∘L Ft ∘L
        ((2 : ℂ)⁻¹ • S)) ∧
    ‖(2 : ℂ)⁻¹ • S‖ ≤ 1 ∧
    ‖((2 : ℂ) ^ (γ₁ + 1))⁻¹ • ((Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt)‖ ≤ 1 := by
  have hFs := assemble_explicit Fs Ft S T Ps Pt C D D' E J hres hN hJ hD
  have hJn := norm_left_inverse_le E J hE hJ
  have hBn : ‖(Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt‖ ≤ 2 ^ (γ₁ + 1) := by
    calc ‖(Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt‖
        ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * ‖D ∘L J ∘L C ∘L Pt‖ := opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * ‖J ∘L C ∘L Pt‖) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * (‖J‖ * ‖C ∘L Pt‖)) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ ‖(Ps.symm : U →L[ℂ] U)‖ * (‖D‖ * (‖J‖ * (‖C‖ * ‖Pt‖))) := by
          gcongr; exact opNorm_comp_le _ _
      _ ≤ 1 * (2 ^ γ₁ * (2 * (1 * 1))) := by gcongr
      _ = 2 ^ (γ₁ + 1) := by ring
  have h2 : ‖(2 : ℂ)‖ = 2 := RCLike.norm_two
  refine ⟨?_, ?_, ?_⟩
  · rw [hFs]
    ext x
    simp only [smul_apply, comp_apply, map_smul, smul_smul]
    convert (one_smul ℂ _).symm using 2
    field_simp
    ring
  · rw [norm_smul, norm_inv, h2]
    calc 2⁻¹ * ‖S‖ ≤ 2⁻¹ * 2 := by gcongr
      _ = 1 := by norm_num
  · rw [norm_smul, norm_inv, norm_pow, h2]
    calc (2 ^ (γ₁ + 1))⁻¹ * ‖(Ps.symm : U →L[ℂ] U) ∘L D ∘L J ∘L C ∘L Pt‖
        ≤ (2 ^ (γ₁ + 1))⁻¹ * 2 ^ (γ₁ + 1) := by gcongr
      _ = 1 := by field_simp

end Explicit

/-! ### The square subsystem as continuous linear maps -/

section Maps

variable (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)

/-- The paper's `C` as a continuous linear map. -/
noncomputable def rowSelectCLM : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  pi fun ℓ => proj (rowIndex s t ℓ)

omit [NeZero s] [NeZero t] in
theorem rowSelectCLM_apply (u : ZMod t → ℂ) : rowSelectCLM s t u = rowSelect s t u := by
  funext ℓ
  simp [rowSelectCLM, rowSelect]

theorem opNorm_rowSelectCLM_le : ‖rowSelectCLM s t‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, rowSelectCLM_apply]
  exact norm_comp_le_pi_norm (rowIndex s t) u

/-- The paper's `D` as a continuous linear map. -/
noncomputable def diagDCLM : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  pi fun ℓ => ((dCoef s t α ℓ.val : ℝ) : ℂ) • proj ℓ

/-- The reciprocal diagonal map `D⁻¹`. -/
noncomputable def diagDInvCLM : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  pi fun ℓ => (((dCoef s t α ℓ.val)⁻¹ : ℝ) : ℂ) • proj ℓ

omit [NeZero t] in
theorem diagDCLM_apply (u : ZMod s → ℂ) : diagDCLM s t α u = diagD s t α u := by
  funext ℓ
  simp [diagDCLM, diagD]

omit [NeZero s] [NeZero t] in
theorem dCoef_pos (ℓ : ℤ) : 0 < dCoef s t α ℓ :=
  lt_of_lt_of_le one_pos (one_le_dCoef s t α ℓ)

omit [NeZero t] in
theorem opNorm_diagDCLM_le : ‖diagDCLM s t α‖ ≤ Real.exp (π * α ^ 2 / 4) := by
  refine opNorm_le_bound _ (Real.exp_pos _).le fun u => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro ℓ
  rw [diagDCLM_apply]
  unfold diagD
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dCoef_pos s t α _)]
  exact mul_le_mul (dCoef_le s t α _) (norm_le_pi_norm u ℓ) (norm_nonneg _) (Real.exp_pos _).le

omit [NeZero s] [NeZero t] in
theorem diagDCLM_comp_inv : diagDCLM s t α ∘L diagDInvCLM s t α = 1 := by
  ext u ℓ
  have h : ((dCoef s t α ℓ.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (dCoef_pos s t α _).ne'
  simp only [comp_apply, diagDCLM, diagDInvCLM, pi_apply, smul_apply, proj_apply,
    smul_eq_mul, Complex.ofReal_inv]
  rw [mul_inv_cancel_left₀ h]
  rfl

/-- The off-diagonal part `E = C T D - 1` as a continuous linear map. -/
noncomputable def offDiagCLM : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  rowSelectCLM s t ∘L resampTCLM s t α ∘L diagDCLM s t α - 1

theorem offDiagCLM_apply (hst : s < t) {α : ℝ} (hα : 0 < α) (u : ZMod s → ℂ) :
    offDiagCLM s t α u = offDiag s t α u := by
  have h := normN_eq s t hst hα u
  simp only [offDiagCLM, sub_apply, comp_apply]
  rw [rowSelectCLM_apply, resampTCLM_apply hα, diagDCLM_apply]
  change normN s t α u - u = _
  rw [h, add_sub_cancel_left]

/-- `C T D = 1 + E`. -/
theorem normN_clm : rowSelectCLM s t ∘L resampTCLM s t α ∘L diagDCLM s t α =
    1 + offDiagCLM s t α := by
  simp [offDiagCLM]

/-- Lemma 4.6 as an operator-norm bound: `‖E‖ ≤ 1/2` when `α² θ ≥ 1`. -/
theorem opNorm_offDiagCLM_le (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) : ‖offDiagCLM s t α‖ ≤ 1 / 2 := by
  refine opNorm_le_of_unit_norm (by norm_num) fun u hu => ?_
  rw [pi_norm_le_iff_of_nonneg (by norm_num), offDiagCLM_apply s t hst hα]
  intro ℓ
  refine norm_offDiag_le_half s t hst hα hθ u (fun j => ?_) ℓ
  rw [← hu]
  exact norm_le_pi_norm u j

/-- `e^{π α² / 4} ≤ 2^{2 ⌈α²⌉}`, since `π / 4 < 2 log 2`. -/
theorem exp_quarter_le_two_pow : Real.exp (π * α ^ 2 / 4) ≤ 2 ^ (2 * ⌈α ^ 2⌉₊) := by
  have hlog := Real.log_two_gt_d9
  have hπ := Real.pi_lt_four
  have hceil : α ^ 2 ≤ ⌈α ^ 2⌉₊ := Nat.le_ceil _
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  calc Real.exp (π * α ^ 2 / 4) ≤ Real.exp (((2 * ⌈α ^ 2⌉₊ : ℕ) : ℝ) * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
    _ = 2 ^ (2 * ⌈α ^ 2⌉₊) := by
        rw [Real.exp_nat_mul, Real.exp_log two_pos]

omit [NeZero t] in
/-- `‖D‖ ≤ 2^{2 ⌈α²⌉}`. -/
theorem opNorm_diagDCLM_le_pow : ‖diagDCLM s t α‖ ≤ 2 ^ (2 * ⌈α ^ 2⌉₊) :=
  (opNorm_diagDCLM_le s t α).trans (exp_quarter_le_two_pow α)

theorem opNorm_resampSCLM_le_two {α : ℝ} (hα : 1 ≤ α) : ‖resampSCLM s t α‖ ≤ 2 := by
  refine (opNorm_resampSCLM_le (by linarith)).trans ?_
  have : 1 / α ≤ 1 := by rw [div_le_one (by linarith)]; exact hα
  linarith

end Maps

/-! ### Proposition 4.7(i) -/

section Factorization

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- Proposition 4.7(i): `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1` and `γ = 2⌈α²⌉ + 2`. -/
theorem resampling_factorization (hst : s < t) (hcop : Nat.Coprime s t) (hα : 1 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) • (B ∘L dftCLM t ∘L A) ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 := by
  have hα0 : 0 < α := by linarith
  have hres := resampling_identity_clm (s := s) (t := t) hα0
  rw [← permSEquiv_coe hcop] at hres
  exact normal_form (dftCLM s) (dftCLM t) (resampSCLM s t α) (resampTCLM s t α)
    (permSEquiv hcop) (permTCLM s) (rowSelectCLM s t) (diagDCLM s t α) (diagDInvCLM s t α)
    (offDiagCLM s t α) (2 * ⌈α ^ 2⌉₊) hres (normN_clm s t α)
    (opNorm_offDiagCLM_le s t hst hα0 hθ) (diagDCLM_comp_inv s t α)
    (opNorm_resampSCLM_le_two s t hα) (opNorm_diagDCLM_le_pow s t α)
    (opNorm_permSEquiv_symm_le hcop) (opNorm_rowSelectCLM_le s t) opNorm_permTCLM_le

/-- The paper's `A = S / 2`. -/
noncomputable def resampA (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  (2 : ℂ)⁻¹ • resampSCLM s t α

/-- The paper's `B = P_s⁻¹ D J C P_t / 2^{γ - 1}` for a left inverse `J` of `N = 1 + E`. -/
noncomputable def resampB (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (hcop : Nat.Coprime s t)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 1))⁻¹ •
    (((permSEquiv hcop).symm : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) ∘L diagDCLM s t α ∘L J ∘L
      rowSelectCLM s t ∘L permTCLM s)

/-- Proposition 4.7(i) with the explicit maps, for any left inverse `J` of `1 + E`. -/
theorem resampling_factorization_explicit (hst : s < t) (hcop : Nat.Coprime s t) (hα : 1 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L (1 + offDiagCLM s t α) = 1) :
    dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB s t α hcop J ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB s t α hcop J‖ ≤ 1 := by
  have hα0 : 0 < α := by linarith
  have hres := resampling_identity_clm (s := s) (t := t) hα0
  rw [← permSEquiv_coe hcop] at hres
  exact normal_form_explicit (dftCLM s) (dftCLM t) (resampSCLM s t α) (resampTCLM s t α)
    (permSEquiv hcop) (permTCLM s) (rowSelectCLM s t) (diagDCLM s t α) (diagDInvCLM s t α)
    (offDiagCLM s t α) J (2 * ⌈α ^ 2⌉₊) hres (normN_clm s t α)
    (opNorm_offDiagCLM_le s t hst hα0 hθ) hJ (diagDCLM_comp_inv s t α)
    (opNorm_resampSCLM_le_two s t hα) (opNorm_diagDCLM_le_pow s t α)
    (opNorm_permSEquiv_symm_le hcop) (opNorm_rowSelectCLM_le s t) opNorm_permTCLM_le

/-- A left inverse `J` of `1 + E` exists with `‖J‖ ≤ 2`. -/
theorem exists_left_inverse (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ), J ∘L (1 + offDiagCLM s t α) = 1 ∧
      (1 + offDiagCLM s t α) ∘L J = 1 ∧ ‖J‖ ≤ 2 := by
  have hE := opNorm_offDiagCLM_le s t hst hα hθ
  obtain ⟨J, h1, h2, -⟩ := exists_inverse_of_norm_lt_one (offDiagCLM s t α) (by linarith)
  exact ⟨J, h1, h2, norm_left_inverse_le _ _ hE h1⟩

end Factorization

end IntegerMultBounds.NLogN
