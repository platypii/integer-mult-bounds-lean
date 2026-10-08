import IntegerMultBounds.NLogN.ResamplingInverse
import IntegerMultBounds.NLogN.Approx

/-! Lemmas 4.8 and 4.11 of Harvey and van der Hoeven, at the level of error
bounds. The off-diagonal map `E` of the normalised resampling system is
approximated by truncating its series to the window `0 < |h| ≤ m`. Proved:
the truncation error is at most `2 A q^m / (1 - q)` with `A = e^{-π α² θ / 2}`
and `q = e^{-4 π α² θ}`, hence at most `3 / 2^p` once `p ≤ 9 m` under
`α² θ ≥ 1`; evaluating the `2m` retained terms with per-term scaled error `c`
costs `2 m c`; and a rounded diagonal entry times a unit-ball input has scaled
error at most `4`. The bit cost of computing the terms is not formalised. -/

namespace IntegerMultBounds.NLogN

open Real

section Window

/-- The index window `0 < |h| ≤ m`. -/
def offDiagWindow (m : ℕ) : Finset ℤ := (Finset.Icc (-(m : ℤ)) m).erase 0

theorem mem_offDiagWindow {m : ℕ} {h : ℤ} :
    h ∈ offDiagWindow m ↔ h ≠ 0 ∧ h.natAbs ≤ m := by
  unfold offDiagWindow
  rw [Finset.mem_erase, Finset.mem_Icc]
  omega

theorem card_offDiagWindow (m : ℕ) : (offDiagWindow m).card = 2 * m := by
  unfold offDiagWindow
  rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

/-- The tail comparison series `A q^{|h|-1}` over `|h| > m` sums to
`2 A q^m / (1 - q)`. -/
theorem hasSum_tail_comparison (A q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun h : ℤ => if m < h.natAbs then A * q ^ (h.natAbs - 1) else 0)
      (A * q ^ m * (1 - q)⁻¹ + A * q ^ m * (1 - q)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · refine (hasSum_nat_add_iff' (m + 1)).mp ?_
    convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left (A * q ^ m) using 1
    · funext n
      have e : ((n + (m + 1) : ℕ) : ℤ).natAbs = n + m + 1 := by omega
      have hc : m < n + m + 1 := by omega
      simp only [e, hc, ↓reduceIte]
      rw [show n + m + 1 - 1 = m + n by omega, pow_add]
      ring
    · rw [Finset.sum_eq_zero, sub_zero]
      intro i hi
      rw [Finset.mem_range] at hi
      have e : ((i : ℕ) : ℤ).natAbs = i := by omega
      have hc : ¬ m < i := by omega
      simp only [e, hc, ↓reduceIte]
  · refine (hasSum_nat_add_iff' m).mp ?_
    convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left (A * q ^ m) using 1
    · funext n
      have e : (-(((n + m : ℕ) : ℤ) + 1)).natAbs = n + m + 1 := by omega
      have hc : m < n + m + 1 := by omega
      simp only [e, hc, ↓reduceIte]
      rw [show n + m + 1 - 1 = m + n by omega, pow_add]
      ring
    · rw [Finset.sum_eq_zero, sub_zero]
      intro i hi
      rw [Finset.mem_range] at hi
      have e : (-(((i : ℕ) : ℤ) + 1)).natAbs = i + 1 := by omega
      have hc : ¬ m < i + 1 := by omega
      simp only [e, hc, ↓reduceIte]

/-- Summing `2m` approximate terms accumulates `2m` times the per-term error. -/
theorem offDiag_sum_err {p : ℕ} {c : ℝ} {I : Finset ℤ} {z' z : ℤ → ℂ}
    (hz : ∀ h ∈ I, (2 : ℝ) ^ p * ‖z' h - z h‖ ≤ c) :
    (2 : ℝ) ^ p * ‖∑ h ∈ I, z' h - ∑ h ∈ I, z h‖ ≤ c * I.card := by
  rw [← Finset.sum_sub_distrib]
  calc (2 : ℝ) ^ p * ‖∑ h ∈ I, (z' h - z h)‖
      ≤ 2 ^ p * ∑ h ∈ I, ‖z' h - z h‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = ∑ h ∈ I, 2 ^ p * ‖z' h - z h‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ h ∈ I, c := Finset.sum_le_sum hz
    _ = c * I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Window

section Trunc

variable (s t : ℕ) [NeZero s] [NeZero t]

/-- The truncated off-diagonal map: the terms of `E` with `0 < |h| ≤ m`. -/
noncomputable def offDiagTrunc (α : ℝ) (m : ℕ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  fun ℓ => ∑ h ∈ offDiagWindow m, (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)

/-- Truncation error of `E` to the window `0 < |h| ≤ m`. -/
theorem offDiag_trunc_err (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (m : ℕ) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤
      2 * Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2) *
        Real.exp (-4 * π * α ^ 2 * ((t : ℝ) / s - 1)) ^ m /
        (1 - Real.exp (-4 * π * α ^ 2 * ((t : ℝ) / s - 1))) := by
  set θ : ℝ := (t : ℝ) / s - 1 with hθdef
  set A : ℝ := Real.exp (-π * α ^ 2 * θ / 2) with hA
  set q : ℝ := Real.exp (-4 * π * α ^ 2 * θ) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq]
    have := Real.exp_lt_exp.mpr (show -4 * π * α ^ 2 * θ < 0 by
      have := Real.pi_pos
      nlinarith)
    simpa using this
  set g : ℤ → ℂ := fun h => (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h) with hg
  set f : ℤ → ℂ := fun h => if h = 0 then 0 else g h with hf
  have hfsum : Summable f := by
    have := (summable_normN_term s t hα u ℓ).update 0 0
    convert this using 1
    funext h
    rw [Function.update_apply]
  set S := offDiagWindow m with hS
  set f₁ : ℤ → ℂ := fun h => if h ∈ S then f h else 0 with hf₁
  set f₂ : ℤ → ℂ := fun h => if h ∈ S then 0 else f h with hf₂
  have hf₁sum : Summable f₁ :=
    summable_of_ne_finset_zero (s := S) (fun h hh => by simp [hf₁, hh])
  have hsplit : f = fun h => f₁ h + f₂ h := by
    funext h
    show f h = (if h ∈ S then f h else 0) + (if h ∈ S then 0 else f h)
    split_ifs <;> simp
  have hf₂sum : Summable f₂ := by
    have : f₂ = fun h => f h - f₁ h := by
      funext h
      show (if h ∈ S then 0 else f h) = f h - (if h ∈ S then f h else 0)
      split_ifs <;> simp
    rw [this]
    exact hfsum.sub hf₁sum
  have htsum : offDiag s t α u ℓ = ∑ h ∈ S, f h + ∑' h, f₂ h := by
    have h1 : offDiag s t α u ℓ = ∑' h, f h := rfl
    have h2 : ∑' h, f h = ∑' h, (f₁ h + f₂ h) := congrArg tsum hsplit
    rw [h1, h2, hf₁sum.tsum_add hf₂sum, tsum_eq_sum (s := S) (fun h hh => by simp [hf₁, hh])]
    congr 1
    exact Finset.sum_congr rfl (fun h hh => by simp [hf₁, hh])
  have htrunc : offDiagTrunc s t α m u ℓ = ∑ h ∈ S, f h := by
    unfold offDiagTrunc
    refine Finset.sum_congr rfl (fun h hh => ?_)
    have : h ≠ 0 := (mem_offDiagWindow.mp hh).1
    simp [hf, hg, this]
  rw [htsum, htrunc, add_sub_cancel_left]
  have hcomp := hasSum_tail_comparison A q hq0 hq1 m
  have hbound : ‖∑' h, f₂ h‖ ≤ A * q ^ m * (1 - q)⁻¹ + A * q ^ m * (1 - q)⁻¹ := by
    refine tsum_of_norm_bounded hcomp (fun h => ?_)
    by_cases hh : h ∈ S
    · have e : f₂ h = 0 := by
        show (if h ∈ S then 0 else f h) = 0
        simp [hh]
      rw [e, norm_zero]
      split_ifs
      · positivity
      · exact le_rfl
    · have hh' := mt mem_offDiagWindow.mpr hh
      by_cases h0 : h = 0
      · subst h0
        have e : f₂ 0 = 0 := by
          show (if (0 : ℤ) ∈ S then 0 else (if (0 : ℤ) = 0 then (0 : ℂ) else g 0)) = 0
          simp
        rw [e, norm_zero]
        simp
      · have hm : m < h.natAbs := by
          by_contra hcon
          exact hh' ⟨h0, not_lt.mp hcon⟩
        have e : f₂ h = g h := by
          show (if h ∈ S then 0 else (if h = 0 then (0 : ℂ) else g h)) = g h
          simp [hh, h0]
        rw [e]
        simp only [hm, ↓reduceIte]
        exact offDiag_term_le s t hst hα u hu ℓ h h0
  calc ‖∑' h, f₂ h‖ ≤ A * q ^ m * (1 - q)⁻¹ + A * q ^ m * (1 - q)⁻¹ := hbound
    _ = 2 * A * q ^ m / (1 - q) := by ring

/-- With `α² θ ≥ 1` and `p ≤ 9 m`, the truncation error is below `3 / 2^p`. -/
theorem offDiag_trunc_err_pow (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : p ≤ 9 * m) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤ 3 / 2 ^ p := by
  refine (offDiag_trunc_err s t hst hα hθ u hu m ℓ).trans ?_
  set θ : ℝ := (t : ℝ) / s - 1 with hθdef
  set A : ℝ := Real.exp (-π * α ^ 2 * θ / 2) with hA
  set q : ℝ := Real.exp (-4 * π * α ^ 2 * θ) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hπ := Real.pi_gt_three
  have hA1 : A ≤ 1 := by
    rw [hA, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq512 : q ≤ 1 / 512 := by
    have h1 : q ≤ Real.exp (-12) := by
      rw [hq]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : Real.exp (-12) ≤ 1 / 625 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) exp_twelve_ge
    linarith
  have h1q : 0 < 1 - q := by linarith
  have hqm : q ^ m ≤ 1 / 2 ^ p := by
    calc q ^ m ≤ (1 / 512) ^ m := pow_le_pow_left₀ hq0 hq512 m
      _ = 1 / 2 ^ (9 * m) := by
          rw [one_div_pow, pow_mul]
          norm_num
      _ ≤ 1 / 2 ^ p := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ (by norm_num) hm
  have hp : (0 : ℝ) < 1 / 2 ^ p := by positivity
  rw [div_le_iff₀ h1q]
  have h1 : 2 * A * q ^ m ≤ 2 * (1 / 2 ^ p) := by
    have := mul_le_mul hA1 hqm (pow_nonneg hq0 m) zero_le_one
    linarith
  have h2 : 2 * (1 / 2 ^ p) ≤ 3 / 2 ^ p * (1 - q) := by
    rw [show (3 : ℝ) / 2 ^ p = 3 * (1 / 2 ^ p) by ring]
    nlinarith
  linarith

/-- Lemma 4.11: evaluating the `2m` retained terms with per-term scaled error `c`
approximates `E` with scaled error `2 m c + 3`. -/
theorem offDiag_approx_err (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : p ≤ 9 * m) (ℓ : ZMod s) {c : ℝ} (z' : ℤ → ℂ)
    (hz : ∀ h ∈ offDiagWindow m,
      (2 : ℝ) ^ p * ‖z' h - (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤ c) :
    (2 : ℝ) ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiag s t α u ℓ‖ ≤ c * (2 * m) + 3 := by
  have hsum := offDiag_sum_err hz
  rw [card_offDiagWindow] at hsum
  have htr := offDiag_trunc_err_pow s t hst hα hθ u hu hm ℓ
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have htr' : (2 : ℝ) ^ p * ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖ ≤ 3 := by
    rw [norm_sub_rev]
    calc (2 : ℝ) ^ p * ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖
        ≤ 2 ^ p * (3 / 2 ^ p) := by gcongr
      _ = 3 := by field_simp
  calc (2 : ℝ) ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiag s t α u ℓ‖
      = 2 ^ p * ‖(∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ) +
          (offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ)‖ := by
        congr 2
        abel
    _ ≤ 2 ^ p * (‖∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ‖ +
          ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖) := by
        gcongr
        exact norm_add_le _ _
    _ = 2 ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ‖ +
          2 ^ p * ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖ := by ring
    _ ≤ c * (2 * m) + 3 := by
        have e : (∑ h ∈ offDiagWindow m, (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)) =
            offDiagTrunc s t α m u ℓ := rfl
        rw [e] at hsum
        push_cast at hsum
        linarith

end Trunc

/-- Lemma 4.8: a rounded real entry in `[0, 1]` times a unit-ball input, rounded
again, has scaled error at most `4`. -/
theorem diag_entry_approx {p : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {u : ℂ}
    (hu : ‖u‖ ≤ 1) :
    (2 : ℝ) ^ p * ‖rhoC p (rhoC p (x : ℂ) * u) - (x : ℂ) * u‖ ≤ 4 := by
  have hx : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h := approx_mul_round (p := p) (η₁ := 2) (η₂ := 0) (u' := rhoC p (x : ℂ))
    (u := (x : ℂ)) (v' := u) (v := u) ((norm_rhoC_le p _).trans hx) hu hx
    (by
      calc (2 : ℝ) ^ p * ‖rhoC p (x : ℂ) - x‖ ≤ 2 ^ p * (2 / 2 ^ p) := by
            gcongr
            exact norm_rhoC_sub_le_two p _
        _ = 2 := by field_simp)
    (by simp)
  linarith

end IntegerMultBounds.NLogN
