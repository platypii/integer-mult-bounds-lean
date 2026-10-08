import IntegerMultBounds.NLogN.OffDiagApproxSqrt
import IntegerMultBounds.NLogN.ResamplingPermutedNumeric

/-! The Neumann evaluation of `J' = N⁻¹/2` as in the manuscript, with no clamp.
The input is halved and rounded first, so it lies in the disk of radius one
half; since `‖E‖ ≤ 0.46` under `α² θ ≥ 1` (the constant `2.01 e^{-π/2}`), every
rounded Horner iterate `y_{i+1} = rd (v - Ẽ y_i)` stays in the unit disk as long
as the scaled error of `Ẽ` on the unit disk is at most `2^p / 25`. The errors
are those of the clamped version, plus the rounding of the halved input carried
through `J`. Hence `B̃₀ = D̃' J̃' C` approximates `B₀` with scaled error
`24 m + 27` and lands in the unit disk without a clamp. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {E : V →L[ℂ] V} {E' rd : V → V} {v : V} {p : ℕ} {εE ρ : ℝ}

/-- The rounded Horner recursion on the unit disk: with `‖E‖ ≤ 0.46`, an input of
norm at most one half and room `εE ≤ 2^p / 25`, the iterates stay in the unit
disk and the scaled error stays below `2 (εE + ρ)`. -/
theorem hornerNeumannR_err_unit (hE : ‖E‖ ≤ 23 / 50)
    (hE' : ∀ y, ‖y‖ ≤ 1 → 2 ^ p * ‖E' y - E y‖ ≤ εE) (hroom : 25 * εE ≤ 2 ^ p)
    (hrd : ∀ x, 2 ^ p * ‖rd x - x‖ ≤ ρ) (hrdball : ∀ x, ‖rd x‖ ≤ ‖x‖)
    (hv : ‖v‖ ≤ 1 / 2) (K : ℕ) :
    ‖hornerNeumannR rd E' v K‖ ≤ 1 ∧
      2 ^ p * ‖hornerNeumannR rd E' v K - hornerNeumann E v K‖ ≤ 2 * (εE + ρ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hεE : 0 ≤ εE := by
    have := hE' v (by linarith)
    have h2 : (0 : ℝ) ≤ 2 ^ p * ‖E' v - E v‖ := by positivity
    linarith
  have hρ : 0 ≤ ρ := by
    have := hrd v
    have h2 : (0 : ℝ) ≤ 2 ^ p * ‖rd v - v‖ := by positivity
    linarith
  have hball' : ∀ y, ‖y‖ ≤ 1 → ‖E' y‖ ≤ 1 / 2 := by
    intro y hy
    have h1 : ‖E' y - E y‖ ≤ εE / 2 ^ p := by
      rw [le_div_iff₀ hp, mul_comm]; exact hE' y hy
    have h2 : ‖E y‖ ≤ 23 / 50 := by
      calc ‖E y‖ ≤ ‖E‖ * ‖y‖ := le_opNorm _ _
        _ ≤ 23 / 50 * 1 := by gcongr
        _ = 23 / 50 := mul_one _
    have h3 : εE / 2 ^ p ≤ 1 / 25 := by
      rw [div_le_iff₀ hp]; linarith
    calc ‖E' y‖ = ‖(E' y - E y) + E y‖ := by rw [sub_add_cancel]
      _ ≤ ‖E' y - E y‖ + ‖E y‖ := norm_add_le _ _
      _ ≤ 1 / 25 + 23 / 50 := by linarith
      _ ≤ 1 / 2 := by norm_num
  have hE2 : ‖E‖ ≤ 1 / 2 := hE.trans (by norm_num)
  induction K with
  | zero =>
    refine ⟨by simpa [hornerNeumannR] using hv.trans (by norm_num), ?_⟩
    simp only [hornerNeumannR, hornerNeumann, sub_self, norm_zero, mul_zero]
    linarith
  | succ K ih =>
    obtain ⟨hball, herr⟩ := ih
    set y' := hornerNeumannR rd E' v K
    set y := hornerNeumann E v K
    refine ⟨?_, ?_⟩
    · calc ‖rd (v - E' y')‖ ≤ ‖v - E' y'‖ := hrdball _
        _ ≤ ‖v‖ + ‖E' y'‖ := norm_sub_le _ _
        _ ≤ 1 / 2 + 1 / 2 := add_le_add hv (hball' _ hball)
        _ = 1 := by norm_num
    · have h1 : 2 ^ p * ‖rd (v - E' y') - (v - E' y')‖ ≤ ρ := hrd _
      have h2 : 2 ^ p * ‖E' y' - E y'‖ ≤ εE := hE' _ hball
      have htri : ‖rd (v - E' y') - (v - E y)‖ ≤
          ‖rd (v - E' y') - (v - E' y')‖ + ‖E' y' - E y'‖ + ‖E y' - E y‖ := by
        have : rd (v - E' y') - (v - E y) =
            (rd (v - E' y') - (v - E' y')) + (E y' - E' y') + (E y - E y') := by abel
        rw [this]
        calc ‖rd (v - E' y') - (v - E' y') + (E y' - E' y') + (E y - E y')‖
            ≤ ‖rd (v - E' y') - (v - E' y') + (E y' - E' y')‖ + ‖E y - E y'‖ :=
              norm_add_le _ _
          _ ≤ ‖rd (v - E' y') - (v - E' y')‖ + ‖E y' - E' y'‖ + ‖E y - E y'‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ = _ := by rw [norm_sub_rev (E y') (E' y'), norm_sub_rev (E y) (E y')]
      have h3 : 2 ^ p * ‖E y' - E y‖ ≤ 1 / 2 * (2 ^ p * ‖y' - y‖) := by
        rw [← map_sub]
        calc 2 ^ p * ‖E (y' - y)‖ ≤ 2 ^ p * (‖E‖ * ‖y' - y‖) := by gcongr; exact le_opNorm _ _
          _ ≤ 2 ^ p * (1 / 2 * ‖y' - y‖) := by gcongr
          _ = 1 / 2 * (2 ^ p * ‖y' - y‖) := by ring
      show 2 ^ p * ‖rd (v - E' y') - id (v - E y)‖ ≤ 2 * (εE + ρ)
      simp only [id]
      calc 2 ^ p * ‖rd (v - E' y') - (v - E y)‖
          ≤ 2 ^ p * (‖rd (v - E' y') - (v - E' y')‖ + ‖E' y' - E y'‖ + ‖E y' - E y‖) := by
            gcongr
        _ = 2 ^ p * ‖rd (v - E' y') - (v - E' y')‖ + 2 ^ p * ‖E' y' - E y'‖ +
              2 ^ p * ‖E y' - E y‖ := by ring
        _ ≤ ρ + εE + 1 / 2 * (2 * (εE + ρ)) := by
            have : 1 / 2 * (2 ^ p * ‖y' - y‖) ≤ 1 / 2 * (2 * (εE + ρ)) := by gcongr
            linarith
        _ = 2 * (εE + ρ) := by ring

/-- Lemma 4.12 on the unit disk: `p` rounded Horner steps from an input of norm
at most one half approximate `J v` with scaled error at most `2 (εE + ρ) + 1`. -/
theorem inverse_approx_unit {J : V →L[ℂ] V} (hE : ‖E‖ ≤ 23 / 50) (hJ : (1 + E) ∘L J = 1)
    (hE' : ∀ y, ‖y‖ ≤ 1 → 2 ^ p * ‖E' y - E y‖ ≤ εE) (hroom : 25 * εE ≤ 2 ^ p)
    (hrd : ∀ x, 2 ^ p * ‖rd x - x‖ ≤ ρ) (hrdball : ∀ x, ‖rd x‖ ≤ ‖x‖)
    (hv : ‖v‖ ≤ 1 / 2) :
    2 ^ p * ‖hornerNeumannR rd E' v p - J v‖ ≤ 2 * (εE + ρ) + 1 := by
  have hE2 : ‖E‖ ≤ 1 / 2 := hE.trans (by norm_num)
  have h1 := (hornerNeumannR_err_unit hE hE' hroom hrd hrdball hv p).2
  have h2 : ‖hornerNeumann E v p - J v‖ ≤ 1 / 2 ^ p := by
    rw [hornerNeumann_eq_partial, ← sub_apply]
    calc ‖(neumannPartial E (p + 1) - J) v‖
        ≤ ‖neumannPartial E (p + 1) - J‖ * ‖v‖ := le_opNorm _ _
      _ ≤ 1 / 2 ^ p * 1 := by
        gcongr
        · exact norm_neumannPartial_sub_inv_pow hE2 hJ p
        · linarith
      _ = 1 / 2 ^ p := mul_one _
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h3 : 2 ^ p * ‖hornerNeumann E v p - J v‖ ≤ 1 := by
    calc 2 ^ p * ‖hornerNeumann E v p - J v‖ ≤ 2 ^ p * (1 / 2 ^ p) := by gcongr
      _ = 1 := by field_simp
  calc 2 ^ p * ‖hornerNeumannR rd E' v p - J v‖
      ≤ 2 ^ p * (‖hornerNeumannR rd E' v p - hornerNeumann E v p‖ +
          ‖hornerNeumann E v p - J v‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR rd E' v p - hornerNeumann E v p‖ +
          2 ^ p * ‖hornerNeumann E v p - J v‖ := by ring
    _ ≤ 2 * (εE + ρ) + 1 := add_le_add h1 h3

end Generic

section Concrete

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- Lemma 4.6 with the constant of the cited proof: `‖E‖ ≤ 0.46`. -/
theorem opNorm_offDiagCLM_le_unit (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) : ‖offDiagCLM s t α‖ ≤ 23 / 50 := by
  refine opNorm_le_of_unit_norm (by norm_num) fun u hu => ?_
  rw [pi_norm_le_iff_of_nonneg (by norm_num), offDiagCLM_apply s t hst hα]
  intro ℓ
  refine (norm_offDiag_le s t hst hα hθ u (fun j => ?_) ℓ).trans ?_
  · rw [← hu]; exact norm_le_pi_norm u j
  have h1 : Real.exp (-Real.pi * α ^ 2 * ((t : ℝ) / s - 1) / 2) ≤ Real.exp (-(Real.pi / 2)) := by
    apply Real.exp_le_exp.mpr
    have := Real.pi_pos
    nlinarith
  have h2 : Real.exp (-(Real.pi / 2)) ≤ 1 / 4.38 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_half_pi_ge
  calc 2.01 * Real.exp (-Real.pi * α ^ 2 * ((t : ℝ) / s - 1) / 2)
      ≤ 2.01 * (1 / 4.38) := by gcongr; linarith
    _ ≤ 23 / 50 := by norm_num

/-- The manuscript's `J̃'`: halve and round the input, then `p` rounded Horner
steps with the unclamped `Ẽ`. -/
noncomputable def resampJNumH (p m : ℕ) (s t : ℕ) [NeZero s] (α : ℝ) (v : ZMod s → ℂ) : ZMod s → ℂ :=
  hornerNeumannR (rdV p) (offDiagNum m (offDiagTermNum p s t α)) (rdV p ((1 / 2 : ℂ) • v)) p

/-- `J̃'` stays in the unit disk and approximates `J (v/2)` with scaled error
`2 (εE + 2) + 5`, for any bound `εE ≤ 2^p/25` on the scaled error of `Ẽ` on the
unit disk. -/
theorem resampJNumH_err (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNumH p m s t α v‖ ≤ 1 ∧
      2 ^ p * ‖resampJNumH p m s t α v - J ((1 / 2 : ℂ) • v)‖ ≤ 2 * (εE + 2) + 5 := by
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hp : (0 : ℝ) < 2 ^ p := by positivity
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
  unfold resampJNumH
  rw [← hv0]
  calc 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offDiagTermNum p s t α)) v0 p - J ((1 / 2 : ℂ) • v)‖
      ≤ 2 ^ p * (‖hornerNeumannR (rdV p) (offDiagNum m (offDiagTermNum p s t α)) v0 p - J v0‖ +
          ‖J v0 - J ((1 / 2 : ℂ) • v)‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offDiagTermNum p s t α)) v0 p - J v0‖ +
          2 ^ p * ‖J v0 - J ((1 / 2 : ℂ) • v)‖ := by ring
    _ ≤ (2 * (εE + 2) + 1) + 4 := add_le_add h1 h2
    _ = 2 * (εE + 2) + 5 := by ring

/-- The manuscript's numerical `B̃₀ = D̃' J̃' C`: no clamp and no final halving. -/
noncomputable def resampB₀NumH (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (w : ZMod t → ℂ) : ZMod s → ℂ :=
  diagDNum p s t α (resampJNumH p m s t α (rowSelect s t w))

/-- `B̃₀` lands in the unit disk on the unit disk. -/
theorem resampB₀NumH_ball (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p) {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    (hJ : (1 + offDiagCLM s t α) ∘L J = 1) (w : ZMod t → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖resampB₀NumH p m s t α w‖ ≤ 1 := by
  have hv1 : ‖rowSelect s t w‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  have hy := (resampJNumH_err hst hα hθ hE' hroom hJ hv1).1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro ℓ
  unfold resampB₀NumH diagDNum
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul]
  have hd : ‖rhoC p (dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    refine (norm_rhoC_le p _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  calc ‖rhoC p (dPrime s t α ℓ : ℂ)‖ * ‖resampJNumH p m s t α (rowSelect s t w) ℓ‖ ≤ 1 * 1 :=
        mul_le_mul hd ((norm_le_pi_norm _ ℓ).trans hy) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Proposition 4.7(ii) for `B₀` in the manuscript's form: `B̃₀` approximates `B₀`
with scaled error `6 + 2 (εE + 2) + 5`. -/
theorem approxMap_resampB₀NumH (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p) {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumH p m s t α) (resampB₀ s t α J) (6 + (2 * (εE + 2) + 5)) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t w with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  set y := resampJNumH p m s t α v with hy
  obtain ⟨hy1, hyJ⟩ := resampJNumH_err hst hα hθ hE' hroom hJ hv1
  have hB : resampB₀ s t α J w ℓ = (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ := by
    rw [resampB₀_apply, map_smul, Pi.smul_apply, smul_eq_mul]; ring
  have hBN : resampB₀NumH p m s t α w ℓ = diagDNum p s t α y ℓ := rfl
  rw [hB, hBN]
  have hD := diagDNum_err (s := s) (t := t) (α := α) p (hy1.trans one_le_two) ℓ
  have hJℓ : 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 * (εE + 2) + 5 := by
    have hk : ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ ‖y - J ((1 / 2 : ℂ) • v)‖ :=
      norm_le_pi_norm (y - J ((1 / 2 : ℂ) • v)) ℓ
    have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
    calc 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 ^ p * ‖y - J ((1 / 2 : ℂ) • v)‖ := by gcongr
      _ ≤ _ := hyJ
  have hd1 : ‖(dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  have hsplit : diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ =
      (diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ) := by ring
  rw [hsplit]
  calc 2 ^ p * ‖(diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ)‖
      ≤ 2 ^ p * (‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by
        gcongr
        rw [← norm_mul]
        exact norm_add_le _ _
    _ = 2 ^ p * ‖diagDNum p s t α y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * (2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by ring
    _ ≤ 6 + 1 * (2 * (εE + 2) + 5) := by gcongr
    _ = 6 + (2 * (εE + 2) + 5) := by ring

/-- The scaled error of the manuscript's `B̃₀` with window radius `m`. -/
noncomputable def errB₀H (m : ℕ) : ℝ := 6 + (2 * ((6 * (2 * (m : ℝ)) + 6) + 2) + 5)

theorem pow_room (p : ℕ) (hp : 13 ≤ p) : 300 * p + 150 ≤ 2 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

theorem sqrtWindow_le_third {p : ℕ} (hp : 13 ≤ p) : 3 * sqrtWindow p ≤ p := by
  unfold sqrtWindow
  have h1 := Nat.sqrt_le' p
  have h2 := Nat.lt_succ_sqrt' p
  generalize Nat.sqrt p = r at h1 h2
  rw [Nat.succ_eq_add_one] at h2
  have hr : 3 ≤ r := by
    by_contra h
    have : r + 1 ≤ 3 := by omega
    have : (r + 1) ^ 2 ≤ 9 := by nlinarith
    omega
  rcases Nat.eq_or_lt_of_le hr with h | h
  · subst h; omega
  · nlinarith

/-- The unclamped `Ẽ` on the unit disk: scaled error `12 m + 6` for windows with `p ≤ 9 m`. -/
theorem offDiagNum_err_unit (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 1) :
    2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 :=
  offDiagNum_err_two hst hα hθ hm (fun _ hu ℓ h _ => offDiagTermNum_err p hu ℓ h) y
    (hy.trans one_le_two)

/-- The same with the square-root window `p ≤ 9 m²`. -/
theorem offDiagNum_err_unit_sqrt (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m ^ 2)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 1) :
    2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 :=
  offDiagNum_err_two_sqrt hst hα hθ hm (fun _ hu ℓ h _ => offDiagTermNum_err p hu ℓ h) y
    (hy.trans one_le_two)

theorem room_of_le {p m : ℕ} (hmp : m ≤ p) (hp : 13 ≤ p) :
    25 * ((6 * (2 * (m : ℝ)) + 6)) ≤ 2 ^ p := by
  have h := pow_room p hp
  have h' : ((300 * p + 150 : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have hm : (m : ℝ) ≤ p := by exact_mod_cast hmp
  nlinarith

/-- `B̃₀` with the square-root window: error `errB₀H (⌊√p⌋ + 1)`, no clamp. -/
theorem approxMap_resampB₀NumH_sqrt (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p : ℕ} (hp : 13 ≤ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumH p (sqrtWindow p) s t α) (resampB₀ s t α J)
      (errB₀H (sqrtWindow p)) :=
  approxMap_resampB₀NumH hst hα hθ
    (offDiagNum_err_unit_sqrt hst hα hθ (sqrtWindow_bound p))
    (room_of_le (sqrtWindow_le p (by omega)) hp) hJ

theorem resampB₀NumH_sqrt_ball (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p : ℕ} (hp : 13 ≤ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    (w : ZMod t → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖resampB₀NumH p (sqrtWindow p) s t α w‖ ≤ 1 :=
  resampB₀NumH_ball hst hα hθ (offDiagNum_err_unit_sqrt hst hα hθ (sqrtWindow_bound p))
    (room_of_le (sqrtWindow_le p (by omega)) hp) hJ w hw

/-- With the square-root window the error of `B̃₀` is below `p²` for `p ≥ 13`. -/
theorem errB₀H_sqrt_lt_sq {p : ℕ} (hp : 13 ≤ p) : errB₀H (sqrtWindow p) < (p : ℝ) ^ 2 := by
  have h := sqrtWindow_le_third hp
  have h' : (3 * (sqrtWindow p : ℝ)) ≤ p := by exact_mod_cast h
  have h2 : (13 : ℝ) ≤ p := by exact_mod_cast hp
  unfold errB₀H
  nlinarith

end Concrete

end IntegerMultBounds.NLogN
