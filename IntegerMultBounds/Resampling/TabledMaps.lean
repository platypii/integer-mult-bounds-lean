import IntegerMultBounds.Resampling.NeumannWords
import IntegerMultBounds.NLogN.ResamplingManuscript

/-! The manuscript's numerical maps with supplied weights. Exact rounding of
an exponential cannot be computed within a provable time bound, so the tape
machines use weight tables that are only within two grid units of the true
weights. The error analysis is unchanged: each fixed-point term keeps its
scaled error (four for `Ã`, six for `Ẽ` and `D̃'`), so `Ã` and the clamp-free
`B̃₀` built from any such tables approximate `A` and `B₀` with errors below
`p²` and send the unit disk to itself. -/

namespace IntegerMultBounds.Resampling.TabledMaps

open IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)
open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

section Terms

omit [NeZero t] in
/-- A Gaussian term with a weight within two grid units has scaled error at most four. -/
theorem termW_err (p : ℕ) (wf : ZMod t → ℤ → ℝ) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 1) (k : ZMod t) (j : ℤ)
    (hwf : 2 ^ p * ‖rhoC p (wf k j : ℂ) - (resampWeight s t α k j : ℂ)‖ ≤ 2) :
    2 ^ p * ‖termW p wf u k j - resampTerm s t α u k j‖ ≤ 4 := by
  rw [resampTerm_eq]
  have h := rhoC_mul_err p hwf ((norm_le_pi_norm u (j : ZMod s)).trans hu)
  unfold termW
  linarith

omit [NeZero t] in
/-- An off-diagonal term with a weight within two grid units has scaled error at
most six on the ball of radius two. -/
theorem offTermW_err (p : ℕ) (ef : ZMod s → ℤ → ℝ) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 2) (ℓ : ZMod s) (h : ℤ)
    (hef : 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2) :
    2 ^ p * ‖offTermW p ef u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ 6 := by
  have hw := rhoC_mul_err p hef ((norm_le_pi_norm u (ℓ + h)).trans hu)
  unfold offTermW offDiagTerm
  linarith

/-- `D̃'` with supplied weights. -/
noncomputable def diagW (p : ℕ) (df : ZMod s → ℝ) (y : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => rhoC p (rhoC p (df ℓ : ℂ) * y ℓ)

omit [NeZero t] in
theorem diagW_err (p : ℕ) (df : ZMod s → ℝ) {y : ZMod s → ℂ} (hy : ‖y‖ ≤ 2) (ℓ : ZMod s)
    (hdf : 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2) :
    2 ^ p * ‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ ≤ 6 := by
  have h := rhoC_mul_err p hdf ((norm_le_pi_norm y ℓ).trans hy)
  unfold diagW
  linarith

end Terms

section Maps

/-- `Ã` with supplied weights approximates `A` with the same error. -/
theorem approxMap_resampANumW (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (wf : ZMod t → ℤ → ℝ)
    (hwf : ∀ k j, 2 ^ p * ‖rhoC p (wf k j : ℂ) - (resampWeight s t α k j : ℂ)‖ ≤ 2) :
    ApproxMap p (resampANum s t m (termW p wf)) (resampA s t α) ((4 * (2 * m + 1) + 3) / 2) :=
  approxMap_resampANum hα hαp hm hm1 fun _ hu k j _ => termW_err p wf hu k j (hwf k j)

/-- `J̃'` with supplied off-diagonal weights. -/
noncomputable def resampJNumW (p m : ℕ) (ef : ZMod s → ℤ → ℝ) (v : ZMod s → ℂ) : ZMod s → ℂ :=
  hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) (rdV p ((1 / 2 : ℂ) • v)) p

theorem resampJNumW_err (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (ef : ZMod s → ℤ → ℝ) {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNumW p m ef v‖ ≤ 1 ∧
      2 ^ p * ‖resampJNumW p m ef v - J ((1 / 2 : ℂ) • v)‖ ≤ 2 * (εE + 2) + 5 := by
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  set v0 := rdV p ((1 / 2 : ℂ) • v) with hv0
  have hhalf : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hv0b : ‖v0‖ ≤ 1 / 2 := (norm_rdV_le p _).trans hhalf
  refine ⟨(hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b p).1, ?_⟩
  have h1 := inverse_approx_unit hE hJ hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b
  have hJ2 := norm_inv_le_two (hE.trans (by norm_num)) hJ
  have h2 : 2 ^ p * ‖J v0 - J ((1 / 2 : ℂ) • v)‖ ≤ 4 := by
    rw [← map_sub]
    calc 2 ^ p * ‖J (v0 - (1 / 2 : ℂ) • v)‖ ≤ 2 ^ p * (‖J‖ * ‖v0 - (1 / 2 : ℂ) • v‖) := by
          gcongr; exact le_opNorm _ _
      _ = ‖J‖ * (2 ^ p * ‖v0 - (1 / 2 : ℂ) • v‖) := by ring
      _ ≤ 2 * 2 := by
          gcongr
          exact norm_rdV_sub_le p _
      _ = 4 := by norm_num
  unfold resampJNumW
  rw [← hv0]
  calc 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 p - J ((1 / 2 : ℂ) • v)‖
      ≤ 2 ^ p * (‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 p - J v0‖ +
          ‖J v0 - J ((1 / 2 : ℂ) • v)‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 p - J v0‖ +
          2 ^ p * ‖J v0 - J ((1 / 2 : ℂ) • v)‖ := by ring
    _ ≤ (2 * (εE + 2) + 1) + 4 := add_le_add h1 h2
    _ = 2 * (εE + 2) + 5 := by ring

/-- `B̃₀ = D̃' J̃' C` with supplied weights. -/
noncomputable def resampB₀NumW (p m : ℕ) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    (w : ZMod t → ℂ) : ZMod s → ℂ :=
  diagW p df (resampJNumW p m ef (rowSelect s t w))

theorem resampB₀NumW_ball (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ) {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p) (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖ ≤ 1)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    (hJ : (1 + offDiagCLM s t α) ∘L J = 1) (w : ZMod t → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖resampB₀NumW p m ef df w‖ ≤ 1 := by
  have hv1 : ‖rowSelect s t w‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  have hy := (resampJNumW_err hst hα hθ ef hE' hroom hJ hv1).1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro ℓ
  unfold resampB₀NumW diagW
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul]
  calc ‖rhoC p (df ℓ : ℂ)‖ * ‖resampJNumW p m ef (rowSelect s t w) ℓ‖ ≤ 1 * 1 :=
        mul_le_mul (hdf1 ℓ) ((norm_le_pi_norm _ ℓ).trans hy) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem approxMap_resampB₀NumW (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ) {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p)
    (hdf : ∀ ℓ, 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumW p m ef df) (resampB₀ s t α J) (6 + (2 * (εE + 2) + 5)) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t w with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  set y := resampJNumW p m ef v with hy
  obtain ⟨hy1, hyJ⟩ := resampJNumW_err hst hα hθ ef hE' hroom hJ hv1
  have hB : resampB₀ s t α J w ℓ = (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ := by
    rw [resampB₀_apply, map_smul, Pi.smul_apply, smul_eq_mul]; ring
  have hBN : resampB₀NumW p m ef df w ℓ = diagW p df y ℓ := rfl
  rw [hB, hBN]
  have hD := diagW_err (t := t) (α := α) p df (hy1.trans one_le_two) ℓ (hdf ℓ)
  have hJℓ : 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 * (εE + 2) + 5 := by
    have hk : ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ ‖y - J ((1 / 2 : ℂ) • v)‖ :=
      norm_le_pi_norm (y - J ((1 / 2 : ℂ) • v)) ℓ
    have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
    calc 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 ^ p * ‖y - J ((1 / 2 : ℂ) • v)‖ := by gcongr
      _ ≤ _ := hyJ
  have hd1 : ‖(dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  have hsplit : diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ =
      (diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ) := by ring
  rw [hsplit]
  calc 2 ^ p * ‖(diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ)‖
      ≤ 2 ^ p * (‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by
        gcongr
        rw [← norm_mul]
        exact norm_add_le _ _
    _ = 2 ^ p * ‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * (2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by ring
    _ ≤ 6 + 1 * (2 * (εE + 2) + 5) := by gcongr
    _ = 6 + (2 * (εE + 2) + 5) := by ring

/-- The off-diagonal map with supplied weights, square-root window, unit disk. -/
theorem offDiagW_err_sqrt (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ}
    (hm : p ≤ 9 * m ^ 2) (ef : ZMod s → ℤ → ℝ)
    (hef : ∀ ℓ h, 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 1) :
    2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 :=
  offDiagNum_err_two_sqrt hst hα hθ hm (fun _ hu ℓ h _ => offTermW_err p ef hu ℓ h (hef ℓ h)) y
    (hy.trans one_le_two)

end Maps

section Tables

/-- An integer table entry within two units of `2^p x` gives the tolerance. -/
theorem tol_of_int (p : ℕ) (W : ℤ) (x : ℝ) (h : |(W : ℝ) - 2 ^ p * x| ≤ 2) :
    2 ^ p * ‖rhoC p (((W : ℝ) / 2 ^ p : ℝ) : ℂ) - (x : ℂ)‖ ≤ 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [WindowSum.rhoC_real, mul_div_cancel₀ _ hp.ne', NeumannWords.rho0_int, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc 2 ^ p * |(W : ℝ) / 2 ^ p - x| = |(W : ℝ) - 2 ^ p * x| := by
        rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp]; congr 1; field_simp
    _ ≤ 2 := h

/-- Lemma 7.1 with the manuscript's maps built from integer weight tables within
two units: both maps approximate with errors below `p²` and map the unit disk to
itself, with the window `⌊√p⌋ + 1` for `B̃₀`. -/
theorem permuted_numeric_tabled (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (WA : ZMod t → ℤ → ℤ) (WE : ZMod s → ℤ → ℤ) (WD : ZMod s → ℤ)
    (hWA : ∀ k j, |(WA k j : ℝ) - 2 ^ p * resampWeight s t α k j| ≤ 2)
    (hWE : ∀ ℓ h, |(WE ℓ h : ℝ) - 2 ^ p * Real.exp (normExp s t α ℓ.val h)| ≤ 2)
    (hWD : ∀ ℓ, |(WD ℓ : ℝ) - 2 ^ p * dPrime s t α ℓ| ≤ 2) (hWD1 : ∀ ℓ, 0 ≤ WD ℓ ∧ WD ℓ ≤ 2 ^ p) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ s t α J ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB₀ s t α J‖ ≤ 1 ∧
      ApproxMap p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p)) (resampA s t α) (errA m) ∧
      ApproxMap p (resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) fun ℓ => (WD ℓ : ℝ) / 2 ^ p)
        (resampB₀ s t α J) (errB₀H (sqrtWindow p)) ∧
      errA m < (p : ℝ) ^ 2 ∧ errB₀H (sqrtWindow p) < (p : ℝ) ^ 2 ∧
      (∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
        ‖resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u‖ ≤ 1) ∧
      (∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 →
        ‖resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) (fun ℓ => (WD ℓ : ℝ) / 2 ^ p) w‖ ≤ 1) := by
  obtain ⟨J, hJ, hJ', hJn⟩ := exists_left_inverse hst (by linarith : (0 : ℝ) < α) hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop (by linarith) hθ J hJ
  have hα0 : (0 : ℝ) < α := by linarith
  have hAx := approxMap_resampANumW (s := s) (t := t) (by linarith) hαp hm hm1 _
    (fun k j => tol_of_int p _ _ (hWA k j))
  have hεA : errA m < (p : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  have hpow : (4 : ℝ) * (p : ℝ) ^ 2 ≤ 2 ^ p := by exact_mod_cast four_sq_le_pow p hp
  have hE' := offDiagW_err_sqrt hst hα0 hθ (sqrtWindow_bound p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p)
    (fun ℓ h => tol_of_int p _ _ (hWE ℓ h))
  have hroom : 25 * (6 * (2 * (sqrtWindow p : ℝ)) + 6) ≤ 2 ^ p := room_of_le (sqrtWindow_le p (by omega)) hp
  have hdf1 : ∀ ℓ, ‖rhoC p ((((WD ℓ : ℝ) / 2 ^ p : ℝ)) : ℂ)‖ ≤ 1 := by
    intro ℓ
    have hp' : (0 : ℝ) < 2 ^ p := by positivity
    rw [WindowSum.rhoC_real, mul_div_cancel₀ _ hp'.ne', NeumannWords.rho0_int, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by exact_mod_cast (hWD1 ℓ).1) hp'.le),
      div_le_one hp']
    exact_mod_cast (hWD1 ℓ).2
  have hBx := approxMap_resampB₀NumW hst hα0 hθ _ _ hE' hroom (fun ℓ => tol_of_int p _ _ (hWD ℓ)) hJ'
  have h4 : 4 * errA m ≤ 2 ^ p := by linarith
  have hA34 := opNorm_resampA_le_three_quarters (s := s) (t := t) hα
  have hAb : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
      ‖resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u‖ ≤ 1 :=
    fun u hu => ball_of_approx hA34 hAx h4 u hu
  have hBb := fun w hw => resampB₀NumW_ball hst hα0 hθ _ _ hE' hroom hdf1 hJ' w hw
  refine ⟨J, ?_, hA, opNorm_resampB₀_le J hJn, hAx, hBx, hεA, errB₀H_sqrt_lt_sq hp, hAb, hBb⟩
  rw [resampB_eq hcop J] at heq
  rw [← permSEquiv_coe hcop, heq]
  ext u j
  simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The Gaussian line machine fed an integer weight table computes `Ã` with that table. -/
theorem accumulators_eq_W (wtWords uWords : List (List Bool)) (s t m p w W : ℕ) [NeZero s] [NeZero t]
    (WA : ZMod t → ℤ → ℤ) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
    (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)
    (hwt' : ∀ k j, k < t → j < 2 * m + 1 →
      Machine.TwosComplement.signed (wtWords.getD (k * (2 * m + 1) + j) []) =
        WA (k : ZMod t) ((Machine.GaussianLine.centre s t k : ℤ) - m + j))
    (hre : ∀ q, q < s + 2 * m → Machine.TwosComplement.signed (uWords.getD (2 * q) []) = ar ((q : ℤ) - m))
    (him : ∀ q, q < s + 2 * m → Machine.TwosComplement.signed (uWords.getD (2 * q + 1) []) = ai ((q : ℤ) - m))
    (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hwt : ∀ x ∈ wtWords, x.length = w) (hul' : ∀ x ∈ uWords, x.length = w)
    (hwb : ∀ x ∈ wtWords, |Machine.TwosComplement.signed x| ≤ 2 ^ p)
    (hub : ∀ x ∈ uWords, |Machine.TwosComplement.signed x| ≤ 2 ^ p)
    (hwtl : wtWords.length = t * (2 * m + 1)) (hul : 2 * (s + 2 * m + 1) ≤ uWords.length)
    (hst : s ≤ t) (hs : 0 < s) (k : ℕ) (hk : k < t) :
    resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u (k : ZMod t) =
      ⟨(Machine.TwosComplement.signed (Machine.GaussianLine.accR wtWords uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1),
       (Machine.TwosComplement.signed (Machine.GaussianLine.accI wtWords uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1)⟩ := by
  have hp' : (0 : ℝ) < 2 ^ p := by positivity
  refine WindowSum.accumulators_eq wtWords uWords s t m p w W (fun k j => (WA k j : ℝ) / 2 ^ p) u ar ai hu
    (fun k j hk hj => ?_) hre him hw hwW hW hwt hul' hwb hub hwtl hul hst hs k hk
  rw [hwt' k j hk hj, mul_div_cancel₀ _ hp'.ne', NeumannWords.rho0_int]

end Tables

end IntegerMultBounds.Resampling.TabledMaps
