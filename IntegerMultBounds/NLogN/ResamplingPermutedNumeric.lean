import IntegerMultBounds.NLogN.ResamplingPermuted
import IntegerMultBounds.NLogN.ExplicitNumeric

/-! The permutation-left resampling identity in `d` dimensions and its numerical
maps (§7, Lemmas 7.1 and 7.2). Tensoring the one-dimensional identity
`P_s F_s = 2^γ B₀ P_t F_t A` gives `R F_s = 2^γ ℬ₀ Q F_t 𝒜` with
`R = ⊗ P_{sᵢ}`, `Q = ⊗ P_{tᵢ}`, `𝒜 = ⊗ Aᵢ`, `ℬ₀ = ⊗ B₀ᵢ`, both tensors
contractions. The numerical `B̃₀ = D̃' J̃ C / 2` needs no permutation; with the
explicit clamped maps of `ExplicitNumeric` the clamped `Ã` and `B̃₀` approximate
`A` and `B₀` with scaled errors `(8m+7)/2` and `(24m+23)/2`, below `p²` for
`m ≤ p` and `p ≥ 13`, hence the linewise tensors with errors below `d p²`.
Costs are not part of this file. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

/-! ### `B₀` entrywise and its numerical version -/

section OneDimensional

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `(B₀ w)_ℓ = (1/2) d'_ℓ (J C w)_ℓ`. -/
theorem resampB₀_apply (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (w : ZMod t → ℂ) (ℓ : ZMod s) :
    resampB₀ s t α J w ℓ =
      (1 / 2 : ℂ) * ((dPrime s t α ℓ : ℂ) * J (rowSelect s t w) ℓ) := by
  unfold resampB₀
  rw [smul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [comp_apply, rowSelectCLM_apply]
  rw [← diagD_scaled_apply, pow_succ, mul_inv]
  ring

/-- The numerical `B̃₀ = D̃' J̃ C / 2` with the clamped `Ẽ`: no permutation. -/
noncomputable def resampB₀Num (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (w : ZMod t → ℂ) : ZMod s → ℂ :=
  (1 / 2 : ℂ) • diagDNum p s t α (resampJNumC p m s t α (rowSelect s t w))

/-- The scaled error of the explicit `Ã` with window radius `m`. -/
noncomputable def errA (m : ℕ) : ℝ := (4 * (2 * (m : ℝ) + 1) + 3) / 2

/-- The scaled error of the explicit `B̃` and `B̃₀` with window radius `m`. -/
noncomputable def errB (m : ℕ) : ℝ := (6 + (2 * ((6 * (2 * (m : ℝ)) + 6) + 2) + 1)) / 2

theorem errA_lt_sq' {p m : ℕ} (hmp : m ≤ p) (hp : 5 ≤ p) : errA m < (p : ℝ) ^ 2 :=
  errA_explicit_lt_sq hmp hp

theorem errB_lt_sq' {p m : ℕ} (hmp : m ≤ p) (hp : 13 ≤ p) : errB m < (p : ℝ) ^ 2 :=
  errB_explicit_lt_sq hmp hp

/-- Proposition 4.7(ii) for `B₀`: `B̃₀` approximates `B₀` with scaled error `errB m`. -/
theorem approxMap_resampB₀Num (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀Num p m s t α) (resampB₀ s t α J) (errB m) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t w with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  set y := resampJNumC p m s t α v with hy
  obtain ⟨hy2, hyJ⟩ := resampJNumC_err hst hα hθ hm hJ hv1
  have hB := resampB₀_apply (α := α) J w ℓ
  have hBN : resampB₀Num p m s t α w ℓ = (1 / 2 : ℂ) * diagDNum p s t α y ℓ := by
    unfold resampB₀Num
    rw [Pi.smul_apply, smul_eq_mul]
  rw [hB, hBN, ← mul_sub, norm_mul, norm_div, norm_one, RCLike.norm_two]
  have hD := diagDNum_err (s := s) (t := t) (α := α) p hy2 ℓ
  have hJℓ : 2 ^ p * ‖y ℓ - J v ℓ‖ ≤ 2 * ((6 * (2 * m) + 6) + 2) + 1 := by
    have hk : ‖y ℓ - J v ℓ‖ ≤ ‖y - J v‖ := norm_le_pi_norm (y - J v) ℓ
    have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
    calc 2 ^ p * ‖y ℓ - J v ℓ‖ ≤ 2 ^ p * ‖y - J v‖ := by gcongr
      _ ≤ _ := hyJ
  have hd1 : ‖(dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  have hsplit : diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * J v ℓ =
      (diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J v ℓ) := by ring
  have hmain : 2 ^ p * ‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * J v ℓ‖ ≤
      6 + (2 * ((6 * (2 * m) + 6) + 2) + 1) := by
    rw [hsplit]
    calc 2 ^ p * ‖(diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
          (dPrime s t α ℓ : ℂ) * (y ℓ - J v ℓ)‖
        ≤ 2 ^ p * (‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
            ‖(dPrime s t α ℓ : ℂ)‖ * ‖y ℓ - J v ℓ‖) := by
          gcongr
          rw [← norm_mul]
          exact norm_add_le _ _
      _ = 2 ^ p * ‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
            ‖(dPrime s t α ℓ : ℂ)‖ * (2 ^ p * ‖y ℓ - J v ℓ‖) := by ring
      _ ≤ 6 + 1 * (2 * ((6 * (2 * m) + 6) + 2) + 1) := by gcongr
      _ = 6 + (2 * ((6 * (2 * m) + 6) + 2) + 1) := by ring
  have e : (2 : ℝ) ^ p * (1 / 2 * ‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * J v ℓ‖) =
      (2 ^ p * ‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * J v ℓ‖) / 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_right hmain (by norm_num)

/-- The clamped explicit `Ã`. -/
noncomputable def resampANumC (p m : ℕ) (s t : ℕ) (α : ℝ) : (ZMod s → ℂ) → ZMod t → ℂ :=
  clampV ∘ resampANum s t m (resampTermNum p s t α)

/-- The clamped explicit `B̃₀`. -/
noncomputable def resampB₀NumC (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod t → ℂ) → ZMod s → ℂ :=
  clampV ∘ resampB₀Num p m s t α

theorem approxMap_resampANumC (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) :
    ApproxMap p (resampANumC p m s t α) (resampA s t α) (errA m) :=
  approxMap_clamp (opNorm_resampA_le hα) (approxMap_resampANum_explicit hα hαp hm hm1)

theorem approxMap_resampB₀NumC (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    (hJn : ‖J‖ ≤ 2) :
    ApproxMap p (resampB₀NumC p m s t α) (resampB₀ s t α J) (errB m) :=
  approxMap_clamp (opNorm_resampB₀_le J hJn) (approxMap_resampB₀Num hst hα hθ hm hJ)

omit [NeZero s] in
theorem resampANumC_ball (p m : ℕ) (u : ZMod s → ℂ) : ‖resampANumC p m s t α u‖ ≤ 1 :=
  norm_clampV_le_one _

theorem resampB₀NumC_ball (p m : ℕ) (w : ZMod t → ℂ) : ‖resampB₀NumC p m s t α w‖ ≤ 1 :=
  norm_clampV_le_one _

/-- Lemma 7.1 with its numerical maps, one dimension: the permutation-left identity
with `A`, `B₀` contractions, and the clamped explicit `Ã`, `B̃₀` with errors below `p²`. -/
theorem permuted_numeric (hst : s < t) (hcop : Nat.Coprime s t) (hα : 1 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hm9 : p ≤ 9 * m) (hmp : m ≤ p)
    (hp : 13 ≤ p) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ s t α J ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB₀ s t α J‖ ≤ 1 ∧
      ApproxMap p (resampANumC p m s t α) (resampA s t α) (errA m) ∧
      ApproxMap p (resampB₀NumC p m s t α) (resampB₀ s t α J) (errB m) ∧
      errA m < (p : ℝ) ^ 2 ∧ errB m < (p : ℝ) ^ 2 := by
  obtain ⟨J, hJ, hJ', hJn⟩ := exists_left_inverse hst (by linarith) hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop hα hθ J hJ
  refine ⟨J, ?_, hA, opNorm_resampB₀_le J hJn, approxMap_resampANumC hα hαp hm hm1,
    approxMap_resampB₀NumC hst (by linarith) hθ hm9 hJ' hJn,
    errA_lt_sq' hmp (by omega), errB_lt_sq' hmp hp⟩
  rw [resampB_eq hcop J] at heq
  rw [← permSEquiv_coe hcop, heq]
  ext u j
  simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end OneDimensional

/-! ### `d` dimensions: `R F_s = 2^γ ℬ₀ Q F_t 𝒜` -/

section Multi

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ}

/-- The retained source permutation `R = ⊗ P_{sᵢ}` as an operator. -/
noncomputable def permRCLM (s t : Fin d → ℕ) [∀ i, NeZero (s i)] :
    (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ) :=
  tensorRCLM fun i => permSCLM (s := s i) (t i)

/-- The retained frequency permutation `Q = ⊗ P_{tᵢ}` as an operator. -/
noncomputable def permQCLM (s t : Fin d → ℕ) [∀ i, NeZero (t i)] :
    (((i : Fin d) → ZMod (t i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ) :=
  tensorRCLM fun i => permTCLM (t := t i) (s i)

/-- Lemma 7.2, exact part: tensoring the permutation-left identity. -/
theorem permuted_factorization_multi (α : ℝ)
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, permSCLM (t i) ∘L dftCLM (s i) = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ (s i) (t i) α (J i) ∘L permTCLM (s i) ∘L dftCLM (t i) ∘L
          resampA (s i) (t i) α)) :
    permRCLM s t ∘L dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
      (tensorRCLM (fun i => resampB₀ (s i) (t i) α (J i)) ∘L permQCLM s t ∘L dftDCLM t ∘L
        tensorRCLM (fun i => resampA (s i) (t i) α)) := by
  unfold permRCLM permQCLM
  rw [dftDCLM_eq_tensor, dftDCLM_eq_tensor, ← tensorRCLM_comp]
  have e : (fun i => permSCLM (t i) ∘L dftCLM (s i)) = fun i =>
      ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) • (resampB₀ (s i) (t i) α (J i) ∘L permTCLM (s i) ∘L
        dftCLM (t i) ∘L resampA (s i) (t i) α) :=
    funext hJ
  rw [e, tensorRCLM_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    mul_comm (2 * ⌈α ^ 2⌉₊ + 2) d,
    tensorRCLM_comp (fun i => resampB₀ (s i) (t i) α (J i))
      (fun i => permTCLM (s i) ∘L dftCLM (t i) ∘L resampA (s i) (t i) α),
    tensorRCLM_comp (fun i => permTCLM (s i)) (fun i => dftCLM (t i) ∘L resampA (s i) (t i) α),
    tensorRCLM_comp (fun i => dftCLM (t i)) (fun i => resampA (s i) (t i) α)]

/-- Lemma 7.2: the `d`-dimensional permutation-left identity with contractions `𝒜`,
`ℬ₀`, and the linewise clamped explicit maps with errors `d·errA`, `d·errB`, each
per-coordinate error below `p²`. -/
theorem permuted_multi_numeric (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1)) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hm9 : p ≤ 9 * m) (hmp : m ≤ p)
    (hp : 13 ≤ p) :
    ∃ J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ),
      permRCLM s t ∘L dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
        (tensorRCLM (fun i => resampB₀ (s i) (t i) α (J i)) ∘L permQCLM s t ∘L dftDCLM t ∘L
          tensorRCLM (fun i => resampA (s i) (t i) α)) ∧
      ‖tensorRCLM (fun i => resampA (s i) (t i) α)‖ ≤ 1 ∧
      ‖tensorRCLM (fun i => resampB₀ (s i) (t i) α (J i))‖ ≤ 1 ∧
      ApproxMap p (tensorZR d s t fun i => resampANumC p m (s i) (t i) α)
        (tensorRCLM fun i => resampA (s i) (t i) α) (d * errA m) ∧
      ApproxMap p (tensorZR d t s fun i => resampB₀NumC p m (s i) (t i) α)
        (tensorRCLM fun i => resampB₀ (s i) (t i) α (J i)) (d * errB m) ∧
      errA m < (p : ℝ) ^ 2 ∧ errB m < (p : ℝ) ^ 2 := by
  have h := fun i => permuted_numeric (hst i) (hcop i) hα (hθ i) hαp hm hm1 hm9 hmp hp
  choose J hJ using h
  refine ⟨J, permuted_factorization_multi α J fun i => (hJ i).1,
    opNorm_tensorRCLM_le _ fun i => (hJ i).2.1, opNorm_tensorRCLM_le _ fun i => (hJ i).2.2.1,
    ?_, ?_, errA_lt_sq' hmp (by omega), errB_lt_sq' hmp hp⟩
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d s t (fun i => resampANumC p m (s i) (t i) α)
      (fun i => resampA (s i) (t i) α) (fun _ => errA m) (fun i => (hJ i).2.1)
      (fun i => (hJ i).2.2.2.1) (fun i v _ => resampANumC_ball p m v)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  · rw [← tensorZRCLM_eq_tensorRCLM]
    have := approxMap_tensorZR d t s (fun i => resampB₀NumC p m (s i) (t i) α)
      (fun i => resampB₀ (s i) (t i) α (J i)) (fun _ => errB m) (fun i => (hJ i).2.2.1)
      (fun i => (hJ i).2.2.2.2.1) (fun i v _ => resampB₀NumC_ball p m v)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

end Multi

end IntegerMultBounds.NLogN
