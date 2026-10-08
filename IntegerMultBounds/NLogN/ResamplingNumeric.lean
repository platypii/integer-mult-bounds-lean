import IntegerMultBounds.NLogN.ResamplingAssembly
import IntegerMultBounds.NLogN.ResamplingApprox
import IntegerMultBounds.NLogN.OffDiagApprox
import IntegerMultBounds.NLogN.NeumannApprox

/-! Proposition 4.7(ii) of Harvey–van der Hoeven: numerical approximations of the
resampling maps `A = S / 2` and `B = P_s⁻¹ D' J' C P_t`. The numerical `Ã` sums
the `2m + 1` retained Gaussian terms of each row of `S`; the numerical `B̃`
applies the exact data moves `P_t`, `C`, then `p` rounded Horner steps of the
Neumann series with the truncated off-diagonal map `Ẽ`, then the rounded
normalised diagonal `D̃'`, then `P_s⁻¹` and a halving. Proved: with per-term
scaled errors `c` for the Gaussian terms (the paper's `7`), `ε(Ã) ≤ (c(2m+1)+3)/2`
and `ε(B̃) ≤ (2(2mc + 8) + 7)/2`, both below `p²` for the paper's parameters.
The fixed-point evaluation of a single Gaussian term, the clamping of `Ẽ` into
the unit ball (taken as a hypothesis), and bit costs are not modeled. -/

namespace IntegerMultBounds.NLogN

open ContinuousLinearMap Real

/-! ### Pointwise approximation on sup-norm spaces -/

section Pointwise

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ℕ}

/-- An entrywise scaled error bound on the unit ball is an `ApproxMap` bound. -/
theorem approxMap_of_pointwise [Nonempty κ] {A' : (ι → ℂ) → (κ → ℂ)}
    {A : (ι → ℂ) →L[ℂ] (κ → ℂ)} {ε : ℝ}
    (h : ∀ v, ‖v‖ ≤ 1 → ∀ k, 2 ^ p * ‖A' v k - A v k‖ ≤ ε) : ApproxMap p A' A ε := by
  intro v hv
  have hε : 0 ≤ ε := le_trans (by positivity) (h v hv (Classical.arbitrary κ))
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [mul_comm, ← le_div_iff₀ hp, pi_norm_le_iff_of_nonneg (div_nonneg hε hp.le)]
  intro k
  rw [le_div_iff₀ hp, mul_comm]
  exact h v hv k

/-- An `ApproxMap` bound gives the entrywise bound. -/
theorem pointwise_of_approxMap {A' : (ι → ℂ) → (κ → ℂ)} {A : (ι → ℂ) →L[ℂ] (κ → ℂ)} {ε : ℝ}
    (h : ApproxMap p A' A ε) {v : ι → ℂ} (hv : ‖v‖ ≤ 1) (k : κ) :
    2 ^ p * ‖A' v k - A v k‖ ≤ ε := by
  have := h v hv
  have hk : ‖A' v k - A v k‖ ≤ ‖A' v - A v‖ := norm_le_pi_norm (A' v - A v) k
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc 2 ^ p * ‖A' v k - A v k‖ ≤ 2 ^ p * ‖A' v - A v‖ := by gcongr
    _ ≤ ε := this

end Pointwise

/-- An approximation of a contraction stays within `ε / 2^p` of the unit ball. -/
theorem norm_le_of_approx {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {ε : ℝ}
    (hA : ‖A‖ ≤ 1) (h : ApproxMap p A' A ε) {v : V} (hv : ‖v‖ ≤ 1) :
    ‖A' v‖ ≤ 1 + ε / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 : ‖A' v - A v‖ ≤ ε / 2 ^ p := by
    rw [le_div_iff₀ hp, mul_comm]
    exact h v hv
  have h2 : ‖A v‖ ≤ 1 := by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  calc ‖A' v‖ = ‖(A' v - A v) + A v‖ := by rw [sub_add_cancel]
    _ ≤ ‖A' v - A v‖ + ‖A v‖ := norm_add_le _ _
    _ ≤ ε / 2 ^ p + 1 := add_le_add h1 h2
    _ = 1 + ε / 2 ^ p := add_comm _ _

/-! ### Componentwise rounding -/

section Rounding

variable {ι : Type*} [Fintype ι] (p : ℕ)

/-- Round every component toward zero at `p` bits. -/
noncomputable def rdV (x : ι → ℂ) : ι → ℂ := fun i => rhoC p (x i)

theorem norm_rdV_le (x : ι → ℂ) : ‖rdV p x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact (norm_rhoC_le p _).trans (norm_le_pi_norm x i)

theorem norm_rdV_sub_le (x : ι → ℂ) : 2 ^ p * ‖rdV p x - x‖ ≤ 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h : ‖rdV p x - x‖ ≤ 2 / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact norm_rhoC_sub_le_two p _
  calc 2 ^ p * ‖rdV p x - x‖ ≤ 2 ^ p * (2 / 2 ^ p) := by gcongr
    _ = 2 := by field_simp

/-- Rounding a product with an approximate first factor. -/
theorem rhoC_mul_err {x' x w : ℂ} {η R : ℝ} (hx' : 2 ^ p * ‖x' - x‖ ≤ η) (hw : ‖w‖ ≤ R) :
    2 ^ p * ‖rhoC p (x' * w) - x * w‖ ≤ 2 + η * R := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hR : 0 ≤ R := (norm_nonneg w).trans hw
  have hη : 0 ≤ η := le_trans (by positivity) hx'
  have h1 := norm_rhoC_sub_le_two p (x' * w)
  have e : rhoC p (x' * w) - x * w = (rhoC p (x' * w) - x' * w) + (x' - x) * w := by ring
  rw [e]
  calc 2 ^ p * ‖(rhoC p (x' * w) - x' * w) + (x' - x) * w‖
      ≤ 2 ^ p * (‖rhoC p (x' * w) - x' * w‖ + ‖(x' - x) * w‖) := by
        gcongr
        exact norm_add_le _ _
    _ = 2 ^ p * ‖rhoC p (x' * w) - x' * w‖ + (2 ^ p * ‖x' - x‖) * ‖w‖ := by
        rw [norm_mul]; ring
    _ ≤ 2 ^ p * (2 / 2 ^ p) + η * R := by gcongr
    _ = 2 + η * R := by field_simp

end Rounding

/-! ### The numerical `Ã = S̃ / 2` -/

section NumA

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The exact `j`-th Gaussian term of row `k` of `S u`, including the `1/α`. -/
noncomputable def resampTerm (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) (k : ZMod t) (j : ℤ) : ℂ :=
  (1 / α : ℂ) * ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j)

/-- The numerical `Ã`: half the sum of the retained fixed-point terms `z' u k j`. -/
noncomputable def resampANum (s t : ℕ) (m : ℕ) (z' : (ZMod s → ℂ) → ZMod t → ℤ → ℂ)
    (u : ZMod s → ℂ) : ZMod t → ℂ :=
  fun k => (1 / 2 : ℂ) * ∑ j ∈ truncWindow s t m k, z' u k j

theorem opNorm_resampA_le (hα : 1 ≤ α) : ‖resampA s t α‖ ≤ 1 := by
  have h := opNorm_resampSCLM_le_two s t hα
  rw [resampA, norm_smul, norm_inv, RCLike.norm_two]
  linarith

/-- Lemma 4.9 packaged: `Ã` approximates `A = S/2` with scaled error `(c(2m+1)+3)/2`
when every retained term is computed with scaled error at most `c`. -/
theorem approxMap_resampANum (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod t → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ∀ k, ∀ j ∈ truncWindow s t m k,
      2 ^ p * ‖z' u k j - resampTerm s t α u k j‖ ≤ c) :
    ApproxMap p (resampANum s t m z') (resampA s t α) ((c * (2 * m + 1) + 3) / 2) := by
  have hα0 : 0 < α := by linarith
  refine approxMap_of_pointwise fun u hu k => ?_
  have hu' : ∀ j, ‖u j‖ ≤ 1 := fun j => (norm_le_pi_norm u j).trans hu
  have h := resampS_approx_err hα hαp hm hm1 u hu' k (z' u k) (hz u hu k)
  have hA : resampA s t α u k = (1 / 2 : ℂ) * resampS s t α u k := by
    unfold resampA
    rw [smul_apply, resampSCLM_apply hα0, Pi.smul_apply, smul_eq_mul, one_div]
  have hN : resampANum s t m z' u k = (1 / 2 : ℂ) * ∑ j ∈ truncWindow s t m k, z' u k j := rfl
  rw [hA, hN, ← mul_sub, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, RCLike.norm_two]
  rw [h12]
  have key : ∀ X : ℝ, (2 : ℝ) ^ p * (1 / 2 * X) = (2 ^ p * X) / 2 := fun X => by ring
  rw [key]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem resampANum_ball (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod t → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ∀ k, ∀ j ∈ truncWindow s t m k,
      2 ^ p * ‖z' u k j - resampTerm s t α u k j‖ ≤ c) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 1) :
    ‖resampANum s t m z' u‖ ≤ 1 + ((c * (2 * m + 1) + 3) / 2) / 2 ^ p := by
  have hAp := approxMap_resampANum hα hαp hm hm1 hz
  have hA1 : ‖resampA s t α‖ ≤ 1 := opNorm_resampA_le hα
  have key := norm_le_of_approx (A := resampA s t α) (A' := resampANum s t m z') hA1 hAp hu
  exact key

end NumA

/-! ### The numerical off-diagonal map `Ẽ` -/

section NumE

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The exact `h`-th term of `(E u)_ℓ`. -/
noncomputable def offDiagTerm (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) (ℓ : ZMod s) (h : ℤ) : ℂ :=
  (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)

/-- The numerical `Ẽ`: the sum of the retained fixed-point terms `z' u ℓ h`. -/
noncomputable def offDiagNum (m : ℕ) (z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ)
    (u : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => ∑ h ∈ offDiagWindow m, z' u ℓ h

/-- Lemma 4.11 packaged on the unit ball. -/
theorem approxMap_offDiagNum (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ c) :
    ApproxMap p (offDiagNum m z') (offDiagCLM s t α) (c * (2 * m) + 3) := by
  refine approxMap_of_pointwise fun u hu ℓ => ?_
  rw [offDiagCLM_apply s t hst hα]
  exact offDiag_approx_err s t hst hα hθ u (fun j => (norm_le_pi_norm u j).trans hu) hm ℓ
    (z' u ℓ) (hz u hu ℓ)

/-- Lemma 4.11 on the ball of radius two, as the Neumann iteration needs it. -/
theorem offDiagNum_err_two (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 2 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ c)
    (u : ZMod s → ℂ) (hu : ‖u‖ ≤ 2) :
    2 ^ p * ‖offDiagNum m z' u - offDiagCLM s t α u‖ ≤ c * (2 * m) + 6 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set u' : ZMod s → ℂ := (1 / 2 : ℂ) • u with hu'def
  have hu' : ‖u'‖ ≤ 1 := by
    rw [hu'def, norm_smul, norm_div, norm_one, RCLike.norm_two]
    linarith
  have hu'' : ∀ j, ‖u' j‖ ≤ 1 := fun j => (norm_le_pi_norm u' j).trans hu'
  -- the entrywise bound
  have hpt : ∀ ℓ, 2 ^ p * ‖offDiagNum m z' u ℓ - offDiagCLM s t α u ℓ‖ ≤ c * (2 * m) + 6 := by
    intro ℓ
    -- scaled terms for `u'`
    have hterm : ∀ h, offDiagTerm s t α u' ℓ h = (1 / 2 : ℂ) * offDiagTerm s t α u ℓ h := by
      intro h
      simp only [offDiagTerm, hu'def, Pi.smul_apply, smul_eq_mul]
      ring
    have hz' : ∀ h ∈ offDiagWindow m, 2 ^ p * ‖(1 / 2 : ℂ) * z' u ℓ h -
        (Real.exp (normExp s t α ℓ.val h) : ℂ) * u' (ℓ + h)‖ ≤ c / 2 := by
      intro h hh
      have e : (Real.exp (normExp s t α ℓ.val h) : ℂ) * u' (ℓ + h) = offDiagTerm s t α u' ℓ h := rfl
      rw [e, hterm, ← mul_sub, norm_mul, norm_div, norm_one, RCLike.norm_two]
      have := hz u hu ℓ h hh
      have e2 : (2 : ℝ) ^ p * (1 / 2 * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖) =
          (2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖) / 2 := by ring
      rw [e2]
      exact div_le_div_of_nonneg_right this (by norm_num)
    have h := offDiag_approx_err s t hst hα hθ u' hu'' hm ℓ (fun h => (1 / 2 : ℂ) * z' u ℓ h) hz'
    rw [← Finset.mul_sum, ← offDiagCLM_apply s t hst hα, hu'def, map_smul, Pi.smul_apply,
      smul_eq_mul, ← mul_sub, norm_mul, norm_div, norm_one, RCLike.norm_two] at h
    have e3 : (2 : ℝ) ^ p * (1 / 2 * ‖∑ x ∈ offDiagWindow m, z' u ℓ x - offDiagCLM s t α u ℓ‖) =
        (2 ^ p * ‖∑ x ∈ offDiagWindow m, z' u ℓ x - offDiagCLM s t α u ℓ‖) / 2 := by ring
    rw [e3] at h
    have hN : offDiagNum m z' u ℓ = ∑ x ∈ offDiagWindow m, z' u ℓ x := rfl
    rw [hN]
    linarith
  have hε : 0 ≤ c * (2 * m) + 6 := le_trans (by positivity) (hpt 0)
  rw [mul_comm, ← le_div_iff₀ hp, pi_norm_le_iff_of_nonneg (div_nonneg hε hp.le)]
  intro ℓ
  rw [le_div_iff₀ hp, mul_comm]
  exact hpt ℓ

end NumE

/-! ### The numerical inverse `J̃` -/

section NumJ

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `p` rounded Horner steps of the Neumann series with the truncated `Ẽ`. -/
noncomputable def resampJNum (p m : ℕ) (z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ)
    (v : ZMod s → ℂ) : ZMod s → ℂ :=
  hornerNeumannR (rdV p) (offDiagNum m z') v p

/-- Lemma 4.12 packaged: `J̃ v` lies in the ball of radius two and approximates
`J v` with scaled error `2 (c(2m) + 6 + 2) + 1`, provided `Ẽ` maps the radius-two
ball into the unit ball (the paper's clamping into `C̃◦`). -/
theorem resampJNum_err (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 2 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ c)
    (hball : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 → ‖offDiagNum m z' y‖ ≤ 1)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNum p m z' v‖ ≤ 2 ∧
      2 ^ p * ‖resampJNum p m z' v - J v‖ ≤ 2 * ((c * (2 * m) + 6) + 2) + 1 := by
  have hE := opNorm_offDiagCLM_le s t hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 →
      2 ^ p * ‖offDiagNum m z' y - offDiagCLM s t α y‖ ≤ c * (2 * m) + 6 :=
    fun y hy => offDiagNum_err_two hst hα hθ hm hz y hy
  exact ⟨(hornerNeumannR_err hE hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv p).1,
    inverse_approx hE hJ hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv⟩

end NumJ

/-! ### The numerical normalised diagonal `D̃'` -/

section NumD

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The normalised diagonal entries `d'_ℓ = d_ℓ / 2^{2⌈α²⌉} ∈ (0, 1]`. -/
noncomputable def dPrime (s t : ℕ) (α : ℝ) (ℓ : ZMod s) : ℝ :=
  dCoef s t α ℓ.val / 2 ^ (2 * ⌈α ^ 2⌉₊)

omit [NeZero s] [NeZero t] in
theorem dPrime_nonneg (ℓ : ZMod s) : 0 ≤ dPrime s t α ℓ :=
  div_nonneg (dCoef_pos s t α _).le (by positivity)

omit [NeZero s] [NeZero t] in
theorem dPrime_le_one (ℓ : ZMod s) : dPrime s t α ℓ ≤ 1 := by
  unfold dPrime
  rw [div_le_one (by positivity)]
  exact (dCoef_le s t α _).trans (exp_quarter_le_two_pow α)

omit [NeZero t] in
/-- `D' = D / 2^{2⌈α²⌉}` entrywise. -/
theorem diagD_scaled_apply (w : ZMod s → ℂ) (ℓ : ZMod s) :
    ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊))⁻¹ * diagDCLM s t α w ℓ = (dPrime s t α ℓ : ℂ) * w ℓ := by
  rw [diagDCLM_apply]
  unfold diagD dPrime
  push_cast
  ring

/-- The numerical `D̃'`: round the entry, multiply, round again. -/
noncomputable def diagDNum (p : ℕ) (s t : ℕ) (α : ℝ) (w : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => rhoC p (rhoC p (dPrime s t α ℓ : ℂ) * w ℓ)

omit [NeZero t] in
/-- Lemma 4.8 on the ball of radius two: each entry has scaled error at most six. -/
theorem diagDNum_err (p : ℕ) {w : ZMod s → ℂ} (hw : ‖w‖ ≤ 2) (ℓ : ZMod s) :
    2 ^ p * ‖diagDNum p s t α w ℓ - (dPrime s t α ℓ : ℂ) * w ℓ‖ ≤ 6 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hx : 2 ^ p * ‖rhoC p (dPrime s t α ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2 := by
    calc 2 ^ p * ‖rhoC p (dPrime s t α ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖
        ≤ 2 ^ p * (2 / 2 ^ p) := by
          gcongr
          exact norm_rhoC_sub_le_two p _
      _ = 2 := by field_simp
  have h := rhoC_mul_err p hx ((norm_le_pi_norm w ℓ).trans hw)
  unfold diagDNum
  linarith

omit [NeZero s] [NeZero t] in
theorem norm_diagDNum_le (p : ℕ) (w : ZMod s → ℂ) (ℓ : ZMod s) :
    ‖diagDNum p s t α w ℓ‖ ≤ ‖w ℓ‖ := by
  unfold diagDNum
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul]
  have h1 : ‖rhoC p (dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    refine (norm_rhoC_le p _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  calc ‖rhoC p (dPrime s t α ℓ : ℂ)‖ * ‖w ℓ‖ ≤ 1 * ‖w ℓ‖ := by gcongr
    _ = ‖w ℓ‖ := one_mul _

end NumD

/-! ### The numerical `B̃` and Proposition 4.7(ii) -/

section NumB

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The numerical `B̃ = P_s⁻¹ D̃' J̃ C P_t / 2`. -/
noncomputable def resampBNum (p m : ℕ) (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ)
    (hcop : Nat.Coprime s t) (z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ) (w : ZMod t → ℂ) :
    ZMod s → ℂ :=
  (1 / 2 : ℂ) • (permSEquiv hcop).symm
    (diagDNum p s t α (resampJNum p m z' (rowSelect s t (permT s w))))

theorem norm_rowSelect_le (u : ZMod t → ℂ) : ‖rowSelect s t u‖ ≤ ‖u‖ :=
  norm_comp_le_pi_norm (rowIndex s t) u

omit [NeZero s] in
theorem norm_permT_le (w : ZMod t → ℂ) : ‖permT s w‖ ≤ ‖w‖ :=
  norm_comp_le_pi_norm (fun k : ZMod t => -((s : ZMod t) * k)) w

/-- `B w` entrywise: `(B w)_ℓ = (1/2) d'_{σ ℓ} (J C P_t w)_{σ ℓ}` with `σ = P_s⁻¹`'s index map. -/
theorem resampB_apply (hcop : Nat.Coprime s t) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (w : ZMod t → ℂ) (ℓ : ZMod s) :
    resampB s t α hcop J w ℓ = (1 / 2 : ℂ) *
      ((dPrime s t α ((mulTEquiv hcop).symm ℓ) : ℂ) *
        J (rowSelect s t (permT s w)) ((mulTEquiv hcop).symm ℓ)) := by
  unfold resampB
  rw [smul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [comp_apply, rowSelectCLM_apply, permTCLM_apply, permSEquiv_symm_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [← diagD_scaled_apply, pow_succ, mul_inv]
  ring

/-- Proposition 4.7(ii) for `B`: with the truncated `Ẽ` evaluated to per-term scaled
error `c` on the radius-two ball and clamped into the unit ball, `B̃` approximates `B`
with scaled error `(6 + 2 (c(2m) + 8) + 1) / 2`. -/
theorem approxMap_resampBNum (hst : s < t) (hcop : Nat.Coprime s t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m) {c : ℝ}
    {z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 2 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ c)
    (hball : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 → ‖offDiagNum m z' y‖ ≤ 1)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampBNum p m s t α hcop z') (resampB s t α hcop J)
      ((6 + (2 * ((c * (2 * m) + 6) + 2) + 1)) / 2) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t (permT s w) with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans ((norm_permT_le w).trans hw)
  set y := resampJNum p m z' v with hy
  obtain ⟨hy2, hyJ⟩ := resampJNum_err hst hα hθ hm hz hball hJ hv1
  set σ := (mulTEquiv hcop).symm ℓ with hσ
  have hB := resampB_apply (α := α) hcop J w ℓ
  have hBN : resampBNum p m s t α hcop z' w ℓ = (1 / 2 : ℂ) * diagDNum p s t α y σ := by
    unfold resampBNum
    rw [Pi.smul_apply, smul_eq_mul, permSEquiv_symm_apply, Function.comp_apply]
  rw [hB, hBN, ← mul_sub, norm_mul, norm_div, norm_one, RCLike.norm_two]
  have hD := diagDNum_err (s := s) (t := t) (α := α) p hy2 σ
  have hJσ : 2 ^ p * ‖y σ - J v σ‖ ≤ 2 * ((c * (2 * m) + 6) + 2) + 1 := by
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
      6 + (2 * ((c * (2 * m) + 6) + 2) + 1) := by
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
      _ ≤ 6 + 1 * (2 * ((c * (2 * m) + 6) + 2) + 1) := by
          gcongr
      _ = 6 + (2 * ((c * (2 * m) + 6) + 2) + 1) := by ring
  have e : (2 : ℝ) ^ p * (1 / 2 * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ‖) =
      (2 ^ p * ‖diagDNum p s t α y σ - (dPrime s t α σ : ℂ) * J v σ‖) / 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_right hmain (by norm_num)

/-- With the paper's per-term error `7` and `m ≤ p`, `ε(Ã) ≤ 7m + 5 < p²` for `p ≥ 8`. -/
theorem errA_lt_sq {p m : ℕ} (hmp : m ≤ p) (hp : 8 ≤ p) :
    (7 * (2 * (m : ℝ) + 1) + 3) / 2 < (p : ℝ) ^ 2 := by
  have h1 : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have h2 : (8 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- With the paper's per-term error `7` and `m ≤ p`, `ε(B̃) < p²` for `p ≥ 15`. -/
theorem errB_lt_sq {p m : ℕ} (hmp : m ≤ p) (hp : 15 ≤ p) :
    (6 + (2 * ((7 * (2 * (m : ℝ)) + 6) + 2) + 1)) / 2 < (p : ℝ) ^ 2 := by
  have h1 : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have h2 : (15 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

end NumB

end IntegerMultBounds.NLogN
