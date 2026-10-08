import IntegerMultBounds.NLogN.ExplicitNumeric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Lemma 4.11 of Harvey and van der Hoeven with the paper's window size. Under
`α² θ ≥ 1` every off-diagonal term of the normalised resampling system is at
most `exp (-2π (|h| - 1/2)²)`, a Gaussian in `|h|`, so truncating the series to
`0 < |h| ≤ m` loses at most `3 exp (-2π (m + 1/2)²)`, which is below `3 / 2^p`
as soon as `p ≤ 9 m²`: a window of order `√p` rather than the `p / 9` of
`OffDiagApprox`. Proved: the Gaussian termwise bound, the truncation bound, the
square-root threshold, and the explicit numerical `Ẽ`, `J̃`, and `B̃` with that
window, with `ε(B̃) < p²` at `m = ⌊√p⌋ + 1`. The bit cost of the terms is not
formalised. -/

namespace IntegerMultBounds.NLogN

open Real

section Term

variable (s t : ℕ) [NeZero s] [NeZero t]

omit [NeZero t] in
/-- Under `α² θ ≥ 1`, the `h`-th off-diagonal term is at most
`exp (-2π (|h| - 1/2)²)`. -/
theorem offDiag_term_le_gauss (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (ℓ : ZMod s) (h : ℤ) (hh : h ≠ 0) :
    ‖(Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤
      Real.exp (-2 * π * ((h.natAbs : ℝ) - 1 / 2) ^ 2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (normExp s t α ℓ.val h) * ‖u (ℓ + h)‖
      ≤ Real.exp (normExp s t α ℓ.val h) * 1 := by
        gcongr
        exact hu _
    _ = Real.exp (normExp s t α ℓ.val h) := mul_one _
    _ ≤ _ := ?_
  apply Real.exp_le_exp.mpr
  have hexp := exponent_ge s t hst (beta s t ℓ.val) (beta s t (ℓ.val + h))
    (abs_beta_le s t _) (abs_beta_le s t _) h hh
  unfold normExp
  rw [Nat.cast_natAbs, Int.cast_abs]
  set θ : ℝ := (t : ℝ) / s - 1
  set y : ℝ := |(h : ℝ)| - 1 / 2
  have hπ : 0 < π := Real.pi_pos
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hπα : 0 ≤ π * α ^ 2 := by positivity
  -- `π α² (…) ≥ π α² · 2 θ y² = 2π (α² θ) y² ≥ 2π y²`
  have h1 := mul_le_mul_of_nonneg_left hexp hπα
  have h2 : 2 * π * y ^ 2 ≤ 2 * π * (α ^ 2 * θ) * y ^ 2 := by
    have : 0 ≤ 2 * π * y ^ 2 := by positivity
    nlinarith
  nlinarith

end Term

section Tail

/-- The Gaussian at `m + 1/2 + n` is at most the Gaussian at `m + 1/2` times
`exp (-2π)^n`. -/
theorem gauss_half_le_geom (m n : ℕ) :
    Real.exp (-2 * π * ((m : ℝ) + 1 / 2 + n) ^ 2) ≤
      Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) * Real.exp (-2 * π) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hπ : 0 < π := Real.pi_pos
  have hm : (0 : ℝ) ≤ m := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have key : ((m : ℝ) + 1 / 2) ^ 2 + n ≤ ((m : ℝ) + 1 / 2 + n) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- `exp (-2π) ≤ 1 / 3`. -/
theorem exp_neg_two_pi_le : Real.exp (-2 * π) ≤ 1 / 3 := by
  have h6 : (7 : ℝ) ≤ Real.exp 6 := by
    have := Real.add_one_le_exp (6 : ℝ)
    linarith
  have hπ := Real.pi_gt_three
  have h1 : Real.exp (-2 * π) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-6) ≤ 1 / 7 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h6
  linarith

end Tail

section Trunc

variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Truncation error of `E` to the window `0 < |h| ≤ m`, Gaussian in `m`. -/
theorem offDiag_trunc_err_sqrt (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (m : ℕ) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤
      3 * Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) := by
  set A : ℝ := Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) with hA
  set q : ℝ := Real.exp (-2 * π) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqpos : 0 < q := Real.exp_pos _
  have hq3 : q ≤ 1 / 3 := exp_neg_two_pi_le
  have hq1 : q < 1 := by linarith
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
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
  -- comparison series `A' q^{|h|-1}` with `A' = A / q^m`, so that `A' q^{|h|-1} = A q^{|h|-m-1}`
  set A' : ℝ := A / q ^ m with hA'
  have hcomp := hasSum_tail_comparison A' q hq0 hq1 m
  have hbound : ‖∑' h, f₂ h‖ ≤ A' * q ^ m * (1 - q)⁻¹ + A' * q ^ m * (1 - q)⁻¹ := by
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
        refine (offDiag_term_le_gauss s t hst hα hθ u hu ℓ h h0).trans ?_
        -- `|h| - 1/2 = m + 1/2 + n` with `n = |h| - m - 1`
        set n : ℕ := h.natAbs - m - 1 with hn
        have hcast : (h.natAbs : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 + n := by
          rw [hn, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hcast]
        have hpow : q ^ (h.natAbs - 1) = q ^ m * q ^ n := by
          rw [← pow_add]
          congr 1
          omega
        calc Real.exp (-2 * π * ((m : ℝ) + 1 / 2 + n) ^ 2) ≤ A * q ^ n := gauss_half_le_geom m n
          _ = A' * q ^ (h.natAbs - 1) := by
              rw [hpow, hA', ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero m hqpos.ne')]
  calc ‖∑' h, f₂ h‖ ≤ A' * q ^ m * (1 - q)⁻¹ + A' * q ^ m * (1 - q)⁻¹ := hbound
    _ = 2 * A / (1 - q) := by
        rw [hA']
        field_simp
        ring
    _ ≤ 3 * A := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith

/-- With `α² θ ≥ 1` and `p ≤ 9 m²`, the truncation error is below `3 / 2^p`:
a window of order `√p`. -/
theorem offDiag_trunc_err_sqrt_pow (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : p ≤ 9 * m ^ 2) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤ 3 / 2 ^ p := by
  refine (offDiag_trunc_err_sqrt s t hst hα hθ u hu m ℓ).trans ?_
  have hπ := Real.pi_gt_d2
  have hlog := Real.log_two_lt_d9
  have hlog0 := Real.log_two_gt_d9
  have hmR : (p : ℝ) ≤ 9 * (m : ℝ) ^ 2 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hexp : Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) ≤ 1 / 2 ^ p := by
    have h1 : Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) ≤ Real.exp (-(p : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      -- `p log 2 ≤ 0.6932 · 9 m² < 6.28 m² ≤ 2π (m + 1/2)²`
      have h2 : (p : ℝ) * Real.log 2 ≤ 9 * (m : ℝ) ^ 2 * 0.6931471808 := by
        have := mul_le_mul hmR hlog.le (Real.log_nonneg (by norm_num)) (by positivity)
        linarith
      have h3 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1 / 2) ^ 2 := by nlinarith
      nlinarith
    have h2 : Real.exp (-(p : ℝ) * Real.log 2) = 1 / 2 ^ p := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), inv_eq_one_div]
    rw [h2] at h1
    exact h1
  calc 3 * Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) ≤ 3 * (1 / 2 ^ p) := by gcongr
    _ = 3 / 2 ^ p := by ring

/-- Lemma 4.11 with the square-root window: evaluating the `2m` retained terms
with per-term scaled error `c` approximates `E` with scaled error `2 m c + 3`. -/
theorem offDiag_approx_err_sqrt (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : p ≤ 9 * m ^ 2) (ℓ : ZMod s) {c : ℝ} (z' : ℤ → ℂ)
    (hz : ∀ h ∈ offDiagWindow m,
      (2 : ℝ) ^ p * ‖z' h - (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤ c) :
    (2 : ℝ) ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiag s t α u ℓ‖ ≤ c * (2 * m) + 3 := by
  have hsum := offDiag_sum_err hz
  rw [card_offDiagWindow] at hsum
  have htr := offDiag_trunc_err_sqrt_pow s t hst hα hθ u hu hm ℓ
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

/-! ### The explicit numerical maps with the square-root window -/

section Numeric

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- Lemma 4.11 on the ball of radius two with the square-root window. -/
theorem offDiagNum_err_two_sqrt (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m ^ 2) {c : ℝ}
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
  have hpt : ∀ ℓ, 2 ^ p * ‖offDiagNum m z' u ℓ - offDiagCLM s t α u ℓ‖ ≤ c * (2 * m) + 6 := by
    intro ℓ
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
    have h := offDiag_approx_err_sqrt s t hst hα hθ u' hu'' hm ℓ
      (fun h => (1 / 2 : ℂ) * z' u ℓ h) hz'
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

/-- The clamped `Ẽ` with the square-root window on the ball of radius two. -/
theorem offDiagNumC_err_two_sqrt (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m ^ 2)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 2) :
    2 ^ p * ‖offDiagNumC p m s t α y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 := by
  have hEy : ‖offDiagCLM s t α y‖ ≤ 1 := by
    calc ‖offDiagCLM s t α y‖ ≤ ‖offDiagCLM s t α‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / 2 * 2 := by
          gcongr
          exact opNorm_offDiagCLM_le s t hst hα hθ
      _ = 1 := by norm_num
  have hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 2 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖offDiagTermNum p s t α u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ 6 :=
    fun u hu ℓ h _ => offDiagTermNum_err p hu ℓ h
  have h1 := offDiagNum_err_two_sqrt hst hα hθ hm hz y hy
  have h2 := norm_clampV_sub_le (offDiagNum m (offDiagTermNum p s t α) y)
    (offDiagCLM s t α y) hEy
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  unfold offDiagNumC
  calc 2 ^ p * ‖clampV (offDiagNum m (offDiagTermNum p s t α) y) - offDiagCLM s t α y‖
      ≤ 2 ^ p * ‖offDiagNum m (offDiagTermNum p s t α) y - offDiagCLM s t α y‖ := by gcongr
    _ ≤ 6 * (2 * m) + 6 := h1

/-- Lemma 4.12 for the clamped `Ẽ` with the square-root window. -/
theorem resampJNumC_err_sqrt (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m ^ 2)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNumC p m s t α v‖ ≤ 2 ∧
      2 ^ p * ‖resampJNumC p m s t α v - J v‖ ≤ 2 * ((6 * (2 * m) + 6) + 2) + 1 := by
  have hE := opNorm_offDiagCLM_le s t hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 →
      2 ^ p * ‖offDiagNumC p m s t α y - offDiagCLM s t α y‖ ≤ 6 * (2 * m) + 6 :=
    fun y hy => offDiagNumC_err_two_sqrt hst hα hθ hm y hy
  have hball : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 2 → ‖offDiagNumC p m s t α y‖ ≤ 1 :=
    fun y _ => offDiagNumC_ball p m y
  exact ⟨(hornerNeumannR_err hE hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv p).1,
    inverse_approx hE hJ hE' hball (norm_rdV_sub_le p) (norm_rdV_le p) hv⟩

/-- Proposition 4.7(ii) for `B` with the square-root window `p ≤ 9 m²`:
`ε(B̃) ≤ (6 + 2(12m + 8) + 1)/2`. -/
theorem approxMap_resampBNumC_sqrt (hst : s < t) (hcop : Nat.Coprime s t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : p ≤ 9 * m ^ 2)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampBNumC p m s t α hcop) (resampB s t α hcop J)
      ((6 + (2 * ((6 * (2 * m) + 6) + 2) + 1)) / 2) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t (permT s w) with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans ((norm_permT_le w).trans hw)
  set y := resampJNumC p m s t α v with hy
  obtain ⟨hy2, hyJ⟩ := resampJNumC_err_sqrt hst hα hθ hm hJ hv1
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

end Numeric

/-! ### The window `m = ⌊√p⌋ + 1` -/

section SqrtWindow

/-- The paper's window size for `Ẽ`, up to constants: `⌊√p⌋ + 1`. -/
def sqrtWindow (p : ℕ) : ℕ := Nat.sqrt p + 1

theorem sqrtWindow_bound (p : ℕ) : p ≤ 9 * sqrtWindow p ^ 2 := by
  have h := Nat.lt_succ_sqrt p
  unfold sqrtWindow
  nlinarith

theorem sqrtWindow_le (p : ℕ) (hp : 2 ≤ p) : sqrtWindow p ≤ p := by
  unfold sqrtWindow
  have := Nat.sqrt_lt_self (by omega : 1 < p)
  omega

theorem one_le_sqrtWindow (p : ℕ) : 1 ≤ sqrtWindow p := by
  unfold sqrtWindow
  omega

/-- With the square-root window the explicit `ε(B̃)` is below `p²` for `p ≥ 13`. -/
theorem errB_sqrt_lt_sq {p : ℕ} (hp : 13 ≤ p) :
    (6 + (2 * ((6 * (2 * (sqrtWindow p : ℝ)) + 6) + 2) + 1)) / 2 < (p : ℝ) ^ 2 :=
  errB_explicit_lt_sq (sqrtWindow_le p (by omega)) hp

end SqrtWindow

end IntegerMultBounds.NLogN
