import IntegerMultBounds.NLogN.Clamp
import IntegerMultBounds.NLogN.ResamplingNumeric
import IntegerMultBounds.NLogN.ResamplingMultiNumeric
import IntegerMultBounds.NLogN.SynthConvApproxD

/-! Explicit numerical maps with hypothesis-free error bounds. The per-term
fixed-point evaluations assumed by `ResamplingNumeric` are defined here as
"round the weight, multiply by the input, round again", with scaled error four
on the unit ball and six on the ball of radius two. The off-diagonal map and the
synthetic FFTs are clamped into the unit ball with `Clamp`, which removes the
ball side conditions of the Neumann iteration, of Proposition 3.3/3.4, and of
the multidimensional resampling tensors. Proved: `ε(Ã) ≤ (8m + 7)/2`,
`ε(B̃) ≤ (24m + 23)/2`, Proposition 4.7(ii) in `d` dimensions with errors
`d ε(Ã)`, `d ε(B̃)`, and the clamped synthetic pipeline with scaled error
`3 log₂ T' + 2`, all with no hypotheses beyond the parameter ranges. Bit costs
of evaluating a Gaussian weight to `p` bits are not modeled. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap Real

/-! ### The Gaussian terms of `S` in fixed point -/

section TermS

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The `j`-th Gaussian weight of row `k` of `S`, including the `1/α`. -/
noncomputable def resampWeight (s t : ℕ) (α : ℝ) (k : ZMod t) (j : ℤ) : ℝ :=
  (1 / α) * Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2)

omit [NeZero s] [NeZero t] in
theorem resampTerm_eq (u : ZMod s → ℂ) (k : ZMod t) (j : ℤ) :
    resampTerm s t α u k j = (resampWeight s t α k j : ℂ) * u j := by
  unfold resampTerm resampWeight
  push_cast
  ring

omit [NeZero s] [NeZero t] in
theorem resampWeight_nonneg (hα : 0 < α) (k : ZMod t) (j : ℤ) :
    0 ≤ resampWeight s t α k j := by
  unfold resampWeight
  positivity

omit [NeZero s] [NeZero t] in
theorem resampWeight_le_one (hα : 1 ≤ α) (k : ZMod t) (j : ℤ) :
    resampWeight s t α k j ≤ 1 := by
  unfold resampWeight
  have h1 : 1 / α ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hα
  have h0 : 0 ≤ π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2 := by positivity
  have h2 : Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc (1 / α) * Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2)
      ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- The fixed-point evaluation of one Gaussian term: round the weight, multiply by
the input, round again. -/
noncomputable def resampTermNum (p : ℕ) (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) (k : ZMod t)
    (j : ℤ) : ℂ :=
  rhoC p (rhoC p (resampWeight s t α k j : ℂ) * u j)

omit [NeZero t] in
/-- Each evaluated term has scaled error at most four on the unit ball. -/
theorem resampTermNum_err (p : ℕ) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 1) (k : ZMod t) (j : ℤ) :
    2 ^ p * ‖resampTermNum p s t α u k j - resampTerm s t α u k j‖ ≤ 4 := by
  rw [resampTerm_eq]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hx : 2 ^ p * ‖rhoC p (resampWeight s t α k j : ℂ) - (resampWeight s t α k j : ℂ)‖ ≤ 2 := by
    calc 2 ^ p * ‖rhoC p (resampWeight s t α k j : ℂ) - (resampWeight s t α k j : ℂ)‖
        ≤ 2 ^ p * (2 / 2 ^ p) := by
          gcongr
          exact norm_rhoC_sub_le_two p _
      _ = 2 := by field_simp
  have h := rhoC_mul_err p hx ((norm_le_pi_norm u (j : ZMod s)).trans hu)
  unfold resampTermNum
  linarith

/-- Lemma 4.9 with no hypotheses beyond the parameter ranges:
`ε(Ã) ≤ (4(2m+1) + 3)/2`. -/
theorem approxMap_resampANum_explicit (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) :
    ApproxMap p (resampANum s t m (resampTermNum p s t α)) (resampA s t α)
      ((4 * (2 * m + 1) + 3) / 2) :=
  approxMap_resampANum hα hαp hm hm1 fun _ hu k j _ => resampTermNum_err p hu k j

end TermS

/-! ### The terms of `E` in fixed point, and the clamped `Ẽ` -/

section TermE

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The fixed-point evaluation of one off-diagonal term. -/
noncomputable def offDiagTermNum (p : ℕ) (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) (ℓ : ZMod s)
    (h : ℤ) : ℂ :=
  rhoC p (rhoC p (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h))

omit [NeZero t] in
/-- Each evaluated term has scaled error at most six on the ball of radius two. -/
theorem offDiagTermNum_err (p : ℕ) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 2) (ℓ : ZMod s) (h : ℤ) :
    2 ^ p * ‖offDiagTermNum p s t α u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ 6 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hx : 2 ^ p * ‖rhoC p (Real.exp (normExp s t α ℓ.val h) : ℂ) -
      (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2 := by
    calc 2 ^ p * ‖rhoC p (Real.exp (normExp s t α ℓ.val h) : ℂ) -
          (Real.exp (normExp s t α ℓ.val h) : ℂ)‖
        ≤ 2 ^ p * (2 / 2 ^ p) := by
          gcongr
          exact norm_rhoC_sub_le_two p _
      _ = 2 := by field_simp
  have hw := rhoC_mul_err p hx ((norm_le_pi_norm u (ℓ + h)).trans hu)
  unfold offDiagTermNum offDiagTerm
  linarith

/-- The clamped numerical off-diagonal map. -/
noncomputable def offDiagNumC (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (u : ZMod s → ℂ) : ZMod s → ℂ :=
  clampV (offDiagNum m (offDiagTermNum p s t α) u)

theorem offDiagNumC_ball (p m : ℕ) (y : ZMod s → ℂ) : ‖offDiagNumC p m s t α y‖ ≤ 1 :=
  norm_clampV_le_one _

/-- Lemma 4.11 for the clamped `Ẽ` on the ball of radius two. -/
theorem offDiagNumC_err_two (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 2) :
    2 ^ p * ‖offDiagNumC p m s t α y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 := by
  have hEy : ‖offDiagCLM s t α y‖ ≤ 1 := by
    calc ‖offDiagCLM s t α y‖ ≤ ‖offDiagCLM s t α‖ * ‖y‖ := le_opNorm _ _
      _ ≤ 1 / 2 * 2 := by
          gcongr
          exact opNorm_offDiagCLM_le s t hst hα hθ
      _ = 1 := by norm_num
  have hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 2 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖offDiagTermNum p s t α u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ 6 :=
    fun u hu ℓ h _ => offDiagTermNum_err p hu ℓ h
  have h1 := offDiagNum_err_two hst hα hθ hm hz y hy
  have h2 := norm_clampV_sub_le (offDiagNum m (offDiagTermNum p s t α) y)
    (offDiagCLM s t α y) hEy
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  unfold offDiagNumC
  calc 2 ^ p * ‖clampV (offDiagNum m (offDiagTermNum p s t α) y) - offDiagCLM s t α y‖
      ≤ 2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ := by gcongr
    _ ≤ 6 * (2 * m) + 6 := h1

end TermE

/-! ### The clamped `J̃` and `B̃` -/

section NumBC

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `p` rounded Horner steps of the Neumann series with the clamped `Ẽ`. -/
noncomputable def resampJNumC (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (v : ZMod s → ℂ) : ZMod s → ℂ :=
  hornerNeumannR (rdV p) (offDiagNumC p m s t α) v p

/-- Lemma 4.12 for the clamped `Ẽ`: no ball hypothesis. -/
theorem resampJNumC_err (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNumC p m s t α v‖ ≤ 2 ∧
      2 ^ p * ‖resampJNumC p m s t α v - J v‖ ≤ 2 * ((6 * (2 * m) + 6) + 2) + 1 := by
  have hE := opNorm_offDiagCLM_le s t hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 →
      2 ^ p * ‖offDiagNumC p m s t α y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 :=
    fun y hy => offDiagNumC_err_two hst hα hθ hm y hy
  have hball : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 → ‖offDiagNumC p m s t α y‖ ≤ 1 :=
    fun y _ => offDiagNumC_ball p m y
  exact ⟨(hornerNeumannR_err hE hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv p).1,
    inverse_approx hE hJ hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv⟩

/-- The numerical `B̃ = P_s⁻¹ D̃' J̃ C P_t / 2` with the clamped `Ẽ`. -/
noncomputable def resampBNumC (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (hcop : Nat.Coprime s t) (w : ZMod t → ℂ) : ZMod s → ℂ :=
  (1 / 2 : ℂ) • (permSEquiv hcop).symm
    (diagDNum p s t α (resampJNumC p m s t α (rowSelect s t (permT s w))))

/-- Proposition 4.7(ii) for `B` with no hypotheses beyond the parameter ranges:
`ε(B̃) ≤ (6 + 2(12m + 8) + 1)/2`. -/
theorem approxMap_resampBNumC (hst : s < t) (hcop : Nat.Coprime s t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampBNumC p m s t α hcop) (resampB s t α hcop J)
      ((6 + (2 * ((6 * (2 * m) + 6) + 2) + 1)) / 2) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t (permT s w) with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans ((norm_permT_le w).trans hw)
  set y := resampJNumC p m s t α v with hy
  obtain ⟨hy2, hyJ⟩ := resampJNumC_err hst hα hθ hm hJ hv1
  set σ := (mulTEquiv hcop).symm ℓ with hσ
  have hB := resampB_apply (α := α) hcop J w ℓ
  have hBN : resampBNumC p m s t α hcop w ℓ = (1 / 2 : ℂ) * diagDNum p s t α y σ := by
    unfold resampBNumC
    rw [Pi.smul_apply, smul_eq_mul, permSEquiv_symm_apply, Function.comp_apply]
  rw [hB, hBN, ← mul_sub, norm_mul, norm_div, norm_one, RCLike.norm_two]
  have hD := diagDNum_err (s := s) (t := t) (α := α) p hy2 σ
  have hJσ : 2 ^ p * ‖y σ - J v σ‖ ≤ 2 * ((6 * (2 * m) + 6) + 2) + 1 := by
    have hk : ‖y σ - J v σ‖ ≤ ‖y - J v‖ := norm_le_pi_norm (y - J v) σ
    have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
    calc 2 ^ p * ‖y σ - J v σ‖ ≤ 2 ^ p * ‖y - J v‖ := by gcongr
      _ ≤ _ := hyJ
  have hd1 : ‖(dPrime s t α σ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg σ)]
    exact dPrime_le_one σ
  have hsplit : diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ =
      (diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * y σ) +
        (dPrime s t α σ : ℂ) * (y σ - J v σ) := by ring
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hmain : 2 ^ p * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ‖ ≤
      6 + (2 * ((6 * (2 * m) + 6) + 2) + 1) := by
    rw [hsplit]
    calc 2 ^ p * ‖(diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * y σ) +
          (dPrime s t α σ : ℂ) * (y σ - J v σ)‖
        ≤ 2 ^ p * (‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * y σ‖ +
            ‖(dPrime s t α σ : ℂ)‖ * ‖y σ - J v σ‖) := by
          gcongr
          rw [← norm_mul]
          exact norm_add_le _ _
      _ = 2 ^ p * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * y σ‖ +
            ‖(dPrime s t α σ : ℂ)‖ * (2 ^ p * ‖y σ - J v σ‖) := by ring
      _ ≤ 6 + 1 * (2 * ((6 * (2 * m) + 6) + 2) + 1) := by
          gcongr
      _ = 6 + (2 * ((6 * (2 * m) + 6) + 2) + 1) := by ring
  have e : (2 : ℝ) ^ p * (1 / 2 * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ‖) =
      (2 ^ p * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ‖) / 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_right hmain (by norm_num)

/-- With `m ≤ p`, the explicit `ε(Ã) = (8m + 7)/2` is below `p²` for `p ≥ 5`. -/
theorem errA_explicit_lt_sq {p m : ℕ} (hmp : m ≤ p) (hp : 5 ≤ p) :
    (4 * (2 * (m : ℝ) + 1) + 3) / 2 < (p : ℝ) ^ 2 := by
  have h1 : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have h2 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- With `m ≤ p`, the explicit `ε(B̃) = (24m + 23)/2` is below `p²` for `p ≥ 13`. -/
theorem errB_explicit_lt_sq {p m : ℕ} (hmp : m ≤ p) (hp : 13 ≤ p) :
    (6 + (2 * ((6 * (2 * (m : ℝ)) + 6) + 2) + 1)) / 2 < (p : ℝ) ^ 2 := by
  have h1 : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have h2 : (13 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

end NumBC

/-! ### Clamping vector-valued arrays -/

section ClampVec

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Clamp every inner coordinate of a `(κ → ℂ)`-valued array. -/
noncomputable def clampVV (x : ι → κ → ℂ) : ι → κ → ℂ := fun j => clampV (x j)

theorem norm_clampVV_le_one (x : ι → κ → ℂ) : ‖clampVV x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact norm_clampV_le_one _

theorem norm_clampVV_sub_le (x w : ι → κ → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖clampVV x - w‖ ≤ ‖x - w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  calc ‖(clampVV x - w) j‖ = ‖clampV (x j) - w j‖ := rfl
    _ ≤ ‖x j - w j‖ := norm_clampV_sub_le _ _ ((norm_le_pi_norm w j).trans hw)
    _ = ‖(x - w) j‖ := rfl
    _ ≤ ‖x - w‖ := norm_le_pi_norm _ j

/-- Clamping an approximation of a contraction keeps its scaled error. -/
theorem approxMap_clampVV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {p : ℕ}
    {A' : V → (ι → κ → ℂ)} {A : V →L[ℂ] (ι → κ → ℂ)} {ε : ℝ}
    (hA : ‖A‖ ≤ 1) (h : ApproxMap p A' A ε) : ApproxMap p (clampVV ∘ A') A ε := by
  intro v hv
  have hAv : ‖A v‖ ≤ 1 := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * 1 := mul_le_mul hA hv (norm_nonneg v) zero_le_one
      _ = 1 := one_mul 1
  calc (2 : ℝ) ^ p * ‖(clampVV ∘ A') v - A v‖
      ≤ 2 ^ p * ‖A' v - A v‖ :=
        mul_le_mul_of_nonneg_left (norm_clampVV_sub_le (A' v) (A v) hAv) (by positivity)
    _ ≤ ε := h v hv

end ClampVec

/-! ### The clamped synthetic transforms and pipeline -/

section SynthC

variable {r : ℕ} [NeZero r] {d : ℕ}

/-- The clamped one-dimensional numerical synthetic FFT. -/
noncomputable def synthFFTNumC (r : ℕ) [NeZero r] (n : ℕ)
    (E : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)) :
    (Fin (2 ^ n) → (Fin r → ℂ)) → (Fin (2 ^ n) → (Fin r → ℂ)) :=
  clampVV ∘ fftNormErr n (wSynth r n) E

theorem approxMap_synthFFTNumC {n p : ℕ} (hr : 2 ^ n ∣ 2 * r)
    {E : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)} (hE : ∀ m k, ‖E m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (synthFFTNumC r n E) (synthDFTCLM r (2 ^ n)) n :=
  approxMap_clampVV (opNorm_synthDFTCLM_le (2 ^ n)) (approxMap_synthFFT hr hE)

theorem synthFFTNumC_ball (n : ℕ) (E : (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (u : Fin (2 ^ n) → (Fin r → ℂ)) : ‖synthFFTNumC r n E u‖ ≤ 1 :=
  norm_clampVV_le_one _

/-- The clamped numerical `d`-dimensional synthetic transform. -/
noncomputable def synthDFTDNumC (r : ℕ) [NeZero r] (e : Fin d → ℕ)
    (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)) :
    (((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) →
      (((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :=
  tensorV d (fun i => 2 ^ e i) fun i => synthFFTNumC r (e i) (E i)

/-- Proposition 3.3 with no ball hypothesis. -/
theorem approxMap_synthDFTDNumC {p : ℕ} (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    {E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hE : ∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p) :
    ApproxMap p (synthDFTDNumC r e E) (synthDFTDCLM r fun i => 2 ^ e i) (∑ i, (e i : ℝ)) :=
  approxMap_tensorV d _ _ _ _ (fun i => opNorm_synthDFTCLM_le (2 ^ e i))
    (fun i => approxMap_synthFFTNumC (hr i) (hE i)) (fun i u _ => synthFFTNumC_ball (e i) (E i) u)

theorem synthDFTDNumC_ball (e : Fin d → ℕ)
    (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (u : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) (hu : ‖u‖ ≤ 1) :
    ‖synthDFTDNumC r e E u‖ ≤ 1 :=
  tensorV_ball d _ _ (fun i u _ => synthFFTNumC_ball (e i) (E i) u) u hu

/-- The clamped numerical pipeline. -/
noncomputable def synthPipeDNumC (r : ℕ) [NeZero r] (e : Fin d → ℕ) (p : ℕ)
    (E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ))
    (u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)) :
    ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ) :=
  let Fu := synthDFTDNumC r e E₁ u
  let Fv := synthDFTDNumC r e E₂ v
  let z := fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j))
  fun j => synthDFTDNumC r e E₃ z (-j)

/-- Proposition 3.4 before scaling, with no ball hypotheses: scaled error
`3 ∑ log₂ t_i + 2`. -/
theorem synthPipeDC_err {p : ℕ} (e : Fin d → ℕ) (hr : ∀ i, 2 ^ e i ∣ 2 * r)
    {E₁ E₂ E₃ : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)}
    (hE₁ : ∀ i m k, ‖E₁ i m k‖ ≤ 1 / 2 ^ p) (hE₂ : ∀ i m k, ‖E₂ i m k‖ ≤ 1 / 2 ^ p)
    (hE₃ : ∀ i m k, ‖E₃ i m k‖ ≤ 1 / 2 ^ p)
    {u v : ((i : Fin d) → Fin (2 ^ e i)) → (Fin r → ℂ)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (j : (i : Fin d) → Fin (2 ^ e i)) :
    2 ^ p * ‖synthPipeDNumC r e p E₁ E₂ E₃ u v j - synthPipeDExact r e u v j‖
      ≤ 3 * (∑ i, (e i : ℝ)) + 2 := by
  set S : ℝ := ∑ i, (e i : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set δ : ℝ := S / 2 ^ p with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set N : Fin d → ℕ := fun i => 2 ^ e i with hN
  set Fu' := synthDFTDNumC r e E₁ u
  set Fv' := synthDFTDNumC r e E₂ v
  set Fu := synthDFTD r N u
  set Fv := synthDFTD r N v
  set z' : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => rdC p ((1 / (r : ℂ)) • negacyclicMul (Fu' j) (Fv' j))
  set z : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
    fun j => (1 / (r : ℂ)) • negacyclicMul (Fu j) (Fv j)
  have herr : ∀ (E : (i : Fin d) → (m : ℕ) → Fin (2 ^ (m + 1)) → (Fin r → ℂ)),
      (∀ i m k, ‖E i m k‖ ≤ 1 / 2 ^ p) →
      ∀ w : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ), ‖w‖ ≤ 1 →
      ∀ k, ‖synthDFTDNumC r e E w k - synthDFTD r N w k‖ ≤ δ := by
    intro E hE w hw k
    have h := approxMap_synthDFTDNumC e hr hE w hw
    rw [synthDFTDCLM_apply] at h
    have h' : ‖synthDFTDNumC r e E w - synthDFTD r N w‖ ≤ δ := by
      rw [hδ, le_div_iff₀ hp, mul_comm]
      exact h
    exact (norm_le_pi_norm _ k).trans h'
  have hFu : ∀ k, ‖Fu' k - Fu k‖ ≤ δ := herr E₁ hE₁ u hu
  have hFv : ∀ k, ‖Fv' k - Fv k‖ ≤ δ := herr E₂ hE₂ v hv
  have hFu1 : ∀ k, ‖Fu k‖ ≤ 1 := fun k =>
    norm_synthDFTD_le (fun j => norm_le_pi_norm u j |>.trans hu) k
  have hFv'1 : ∀ k, ‖Fv' k‖ ≤ 1 := fun k =>
    (norm_le_pi_norm _ k).trans (synthDFTDNumC_ball e E₂ v hv)
  have hFu'1 : ∀ k, ‖Fu' k‖ ≤ 1 := fun k =>
    (norm_le_pi_norm _ k).trans (synthDFTDNumC_ball e E₁ u hu)
  have hz : ∀ k, ‖z' k - z k‖ ≤ 2 / 2 ^ p + 2 * δ := by
    intro k
    set x := (1 / (r : ℂ)) • negacyclicMul (Fu' k) (Fv' k)
    calc ‖z' k - z k‖ = ‖(rdC p x - x) + (x - z k)‖ := by
          simp only [z', z, x]; congr 1; abel
      _ ≤ ‖rdC p x - x‖ + ‖x - z k‖ := norm_add_le _ _
      _ ≤ 2 / 2 ^ p + 2 * δ := by
          gcongr
          · exact norm_rdC_sub_le p x
          · exact normProd_err_ball (hFu1 k) (hFv'1 k) (hFu k) (hFv k)
  have hz'1 : ‖z'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    refine (norm_rdC_le p _).trans ?_
    refine (norm_normProd_le _ _).trans ?_
    calc ‖Fu' k‖ * ‖Fv' k‖ ≤ 1 * 1 := by gcongr; exacts [hFu'1 k, hFv'1 k]
      _ = 1 := one_mul 1
  have hexact : synthPipeDExact r e u v j = synthDFTD r N z (-j) := rfl
  have happrox : synthPipeDNumC r e p E₁ E₂ E₃ u v j = synthDFTDNumC r e E₃ z' (-j) := rfl
  rw [hexact, happrox]
  have hsub : ∀ k, ‖synthDFTD r N z' k - synthDFTD r N z k‖ ≤ 2 / 2 ^ p + 2 * δ := by
    intro k
    rw [synthDFTD_sub_apply]
    exact norm_synthDFTD_le hz k
  have htotal : ‖synthDFTDNumC r e E₃ z' (-j) - synthDFTD r N z (-j)‖
      ≤ δ + (2 / 2 ^ p + 2 * δ) := by
    calc ‖synthDFTDNumC r e E₃ z' (-j) - synthDFTD r N z (-j)‖
        = ‖(synthDFTDNumC r e E₃ z' (-j) - synthDFTD r N z' (-j))
            + (synthDFTD r N z' (-j) - synthDFTD r N z (-j))‖ := by
          congr 1; abel
      _ ≤ ‖synthDFTDNumC r e E₃ z' (-j) - synthDFTD r N z' (-j)‖
            + ‖synthDFTD r N z' (-j) - synthDFTD r N z (-j)‖ := norm_add_le _ _
      _ ≤ δ + (2 / 2 ^ p + 2 * δ) := add_le_add (herr E₃ hE₃ z' hz'1 (-j)) (hsub (-j))
  calc 2 ^ p * ‖synthDFTDNumC r e E₃ z' (-j) - synthDFTD r N z (-j)‖
      ≤ 2 ^ p * (δ + (2 / 2 ^ p + 2 * δ)) := by gcongr
    _ = 3 * S + 2 := by rw [hδ]; field_simp; ring

end SynthC

/-! ### Theorem 4.1's numerical half with explicit clamped maps -/

section Multi

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] {α : ℝ}

/-- Proposition 4.7(ii) in `d` dimensions with the explicit clamped maps: the exact
factorization together with `ε(⊗Ã_i) ≤ d (8m + 7)/2` and `ε(⊗B̃_i) ≤ d (24m + 23)/2`. -/
theorem resampling_multi_numeric_explicit {p m : ℕ} (hst : ∀ i, s i < t i)
    (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 1 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / (s i) - 1))
    (hαp : α ^ 2 ≤ p) (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hm9 : p ≤ 9 * m)
    (J : (i : Fin d) → (ZMod (s i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ))
    (hJ : ∀ i, J i ∘L (1 + offDiagCLM (s i) (t i) α) = 1)
    (hJ' : ∀ i, (1 + offDiagCLM (s i) (t i) α) ∘L J i = 1) :
    dftDCLM s = ((2 : ℂ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2))) •
        (tensorRCLM (fun i => resampB (s i) (t i) α (hcop i) (J i)) ∘L dftDCLM t ∘L
          tensorRCLM (fun i => resampA (s i) (t i) α)) ∧
      ApproxMap p
        (tensorZR d s t fun i =>
          clampV ∘ resampANum (s i) (t i) m (resampTermNum p (s i) (t i) α))
        (tensorRCLM (fun i => resampA (s i) (t i) α)) (d * ((4 * (2 * m + 1) + 3) / 2)) ∧
      ApproxMap p (tensorZR d t s fun i => clampV ∘ resampBNumC p m (s i) (t i) α (hcop i))
        (tensorRCLM (fun i => resampB (s i) (t i) α (hcop i) (J i)))
        (d * ((6 + (2 * ((6 * (2 * m) + 6) + 2) + 1)) / 2)) := by
  have hα0 : 0 < α := by linarith
  have hnorm := fun i =>
    (resampling_factorization_explicit (hst i) (hcop i) hα (hθ i) (J i) (hJ i)).2.2
  exact resampling_multi_numeric hst hcop hα hθ J hJ _ _
    (fun i => approxMap_clamp (opNorm_resampA_le hα) (approxMap_resampANum_explicit hα hαp hm hm1))
    (fun i => approxMap_clamp (hnorm i)
      (approxMap_resampBNumC (hst i) (hcop i) hα0 (hθ i) hm9 (hJ' i)))
    (fun i v _ => clamp_ball _ v) (fun i v _ => clamp_ball _ v)

end Multi

end IntegerMultBounds.NLogN
