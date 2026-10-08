import IntegerMultBounds.NLogN.ResamplingNorm
import IntegerMultBounds.NLogN.Approx
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Truncation of the Gaussian resampling series (Lemma 4.9 of Harvey and
van der Hoeven). Proved: keeping only the `2m + 1` terms whose index lies within
`m` of the centre `s k / t` changes row `k` of `S u` by at most `(2/α)` times a
one-sided Gaussian tail; under the paper's parameter constraints `α² ≤ p` and
`p α² ≤ m²` that tail is below `(7/6) 2^(-p)`, so the truncation error is at
most `3 / (α 2^p)`; and a fixed-point evaluation of the truncated sum whose
`2m + 1` terms each carry scaled error at most `c` approximates `S u` with
scaled error at most `c (2m + 1) + 3` when `α ≥ 1`. The per-term fixed-point
computation of a Gaussian weight and the bit costs are not part of this file. -/

namespace IntegerMultBounds.NLogN

open Real

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The centre `s k / t` of the Gaussian weights in row `k`. -/
noncomputable def resampCentre (s t : ℕ) (k : ZMod t) : ℝ := (s : ℝ) * k.val / t

/-- The `2m + 1` integers within `m` of the rounded-down centre. -/
noncomputable def truncWindow (s t : ℕ) (m : ℕ) (k : ZMod t) : Finset ℤ :=
  Finset.Icc (⌊resampCentre s t k⌋ - m) (⌊resampCentre s t k⌋ + m)

omit [NeZero s] [NeZero t] in
theorem card_truncWindow (m : ℕ) (k : ZMod t) : (truncWindow s t m k).card = 2 * m + 1 := by
  unfold truncWindow
  rw [Int.card_Icc]
  omega

/-- The truncated resampling map: the series of `S` restricted to the window. -/
noncomputable def resampSTrunc (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (m : ℕ)
    (u : ZMod s → ℂ) : ZMod t → ℂ :=
  fun k => (1 / α : ℂ) * ∑ j ∈ truncWindow s t m k,
    (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j

/-- Gaussian mass outside the window around `⌊x⌋`, bounded by two one-sided tails. -/
theorem tsum_outside_le_aux {c : ℝ} (hc : 0 < c) (x : ℝ) (m : ℕ) (g : ℤ → ℝ)
    (hg0 : ∀ j, j ∈ Finset.Icc (⌊x⌋ - m) (⌊x⌋ + m) → g j = 0)
    (hg1 : ∀ j, j ∉ Finset.Icc (⌊x⌋ - m) (⌊x⌋ + m) → g j = gauss c (-x + j)) :
    ∑' j : ℤ, g j ≤ 2 * ∑' n : ℕ, gauss c (m + n) := by
  have hax : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hxa : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  generalize ha : ⌊x⌋ = a at *
  have hw : Summable (fun j : ℤ => gauss c (-x + j)) := summable_gauss_int hc _
  have hg_le : ∀ j, g j ≤ gauss c (-x + j) := by
    intro j
    by_cases hj : j ∈ Finset.Icc (a - m) (a + m)
    · rw [hg0 j hj]; exact (gauss_pos _ _).le
    · rw [hg1 j hj]
  have hg_nn : ∀ j, 0 ≤ g j := by
    intro j
    by_cases hj : j ∈ Finset.Icc (a - m) (a + m)
    · rw [hg0 j hj]
    · rw [hg1 j hj]; exact (gauss_pos _ _).le
  have hgs : Summable g := hw.of_nonneg_of_le hg_nn hg_le
  have hT : Summable (fun n : ℕ => gauss c (m + n)) := summable_gauss_nat hc _
  -- Shift the index so that the centre is at `0`.
  let F : ℤ → ℝ := fun j => g (j + a)
  have hF : Summable F := (Equiv.addRight a).summable_iff.mpr hgs
  have hshift : ∑' j : ℤ, g j = ∑' j : ℤ, F j := by
    rw [← (Equiv.addRight a).tsum_eq g]; rfl
  have hpos : Summable (fun n : ℕ => F n) := hF.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) :=
    hF.comp_injective (fun a b h => by omega)
  rw [hshift, tsum_of_nat_of_neg_add_one (f := F) hpos hneg]
  -- Positive side: the first `m + 1` terms vanish, the rest is dominated.
  have hpos_le : ∑' n : ℕ, F n ≤ ∑' n : ℕ, gauss c (m + n) := by
    have h1 : Summable (fun n : ℕ => F ((n + (m + 1) : ℕ) : ℤ)) :=
      (summable_nat_add_iff (f := fun n : ℕ => F n) (m + 1)).mpr hpos
    rw [← Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => F n) (k := m + 1) h1]
    have hzero : ∑ i ∈ Finset.range (m + 1), F (i : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hg0 _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hzero, zero_add]
    refine h1.tsum_le_tsum (fun i => ?_) hT
    have hmem : (((i + (m + 1) : ℕ) : ℤ) + a) ∉ Finset.Icc (a - m) (a + m) := by
      rw [Finset.mem_Icc]; omega
    show g (((i + (m + 1) : ℕ) : ℤ) + a) ≤ gauss c (m + i)
    rw [hg1 _ hmem]
    refine gauss_antitone_abs hc.le ?_
    have h' : ((((i + (m + 1) : ℕ) : ℤ) + a : ℤ) : ℝ) = i + m + 1 + a := by push_cast; ring
    rw [h', abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
    linarith
  -- Negative side: the first `m` terms vanish, the rest is dominated.
  have hneg_le : ∑' n : ℕ, F (-((n : ℤ) + 1)) ≤ ∑' n : ℕ, gauss c (m + n) := by
    have h1 : Summable (fun n : ℕ => F (-(((n + m : ℕ) : ℤ) + 1))) :=
      (summable_nat_add_iff (f := fun n : ℕ => F (-((n : ℤ) + 1))) m).mpr hneg
    rw [← Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => F (-((n : ℤ) + 1))) (k := m) h1]
    have hzero : ∑ i ∈ Finset.range m, F (-((i : ℤ) + 1)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hg0 _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hzero, zero_add]
    refine h1.tsum_le_tsum (fun i => ?_) hT
    have hmem : (-(((i + m : ℕ) : ℤ) + 1) + a) ∉ Finset.Icc (a - m) (a + m) := by
      rw [Finset.mem_Icc]; omega
    show g (-(((i + m : ℕ) : ℤ) + 1) + a) ≤ gauss c (m + i)
    rw [hg1 _ hmem]
    refine gauss_antitone_abs hc.le ?_
    have h' : ((-(((i + m : ℕ) : ℤ) + 1) + a : ℤ) : ℝ) = -(i + m + 1) + a := by push_cast; ring
    rw [h', abs_of_nonneg (by positivity), abs_of_nonpos (by linarith)]
    linarith
  linarith

theorem tsum_outside_window_le {c : ℝ} (hc : 0 < c) (x : ℝ) (m : ℕ) :
    ∑' j : ℤ, (if j ∈ Finset.Icc (⌊x⌋ - m) (⌊x⌋ + m) then 0 else gauss c (-x + j)) ≤
      2 * ∑' n : ℕ, gauss c (m + n) :=
  tsum_outside_le_aux hc x m _ (fun j hj => by simp only [hj, ↓reduceIte])
    (fun j hj => by simp only [hj, ↓reduceIte])

/-- Truncation error of row `k`, in terms of a one-sided Gaussian tail. -/
theorem resampS_trunc_err (hα : 0 < α) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1) (m : ℕ)
    (k : ZMod t) :
    ‖resampS s t α u k - resampSTrunc s t α m u k‖ ≤
      (2 / α) * ∑' n : ℕ, gauss (π * α⁻¹ ^ 2) (m + n) := by
  have hc : 0 < π * α⁻¹ ^ 2 := by positivity
  set f : ℤ → ℂ := fun j =>
    (Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j with hf
  have hfs : Summable f := summable_resampS_term hα u k
  have hterm : ∀ j : ℤ, ‖f j‖ ≤ gauss (π * α⁻¹ ^ 2) (-(resampCentre s t k) + j) := by
    intro j
    simp only [hf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      resamp_weight_eq hα k j]
    unfold resampCentre
    calc gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) * ‖u j‖
        ≤ gauss (π * α⁻¹ ^ 2) (-(s * k.val / t) + j) * 1 :=
          mul_le_mul_of_nonneg_left (hu j) (gauss_pos _ _).le
      _ = _ := mul_one _
  have hw : Summable (fun j : ℤ => gauss (π * α⁻¹ ^ 2) (-(resampCentre s t k) + j)) :=
    summable_gauss_int hc _
  have hfn : Summable (fun j : ℤ => ‖f j‖) := hw.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have h1 : ‖(1 / α : ℂ)‖ = 1 / α := by
    rw [show (1 / α : ℂ) = ((1 / α : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hdiff : resampS s t α u k - resampSTrunc s t α m u k =
      (1 / α : ℂ) * ∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ, f j := by
    have h := hfs.sum_add_tsum_compl (s := truncWindow s t m k)
    show (1 / α : ℂ) * ∑' j : ℤ, f j - (1 / α : ℂ) * ∑ j ∈ truncWindow s t m k, f j = _
    rw [← mul_sub, ← h]
    ring
  rw [hdiff, norm_mul, h1]
  have hsub : Summable (fun j : ↑((truncWindow s t m k : Set ℤ))ᶜ => ‖f j‖) :=
    hfn.subtype _
  calc (1 / α) * ‖∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ, f j‖
      ≤ (1 / α) * ∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ, ‖f j‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsub) (by positivity)
    _ ≤ (1 / α) * ∑' j : ↑((truncWindow s t m k : Set ℤ))ᶜ,
          gauss (π * α⁻¹ ^ 2) (-(resampCentre s t k) + j) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hsub.tsum_le_tsum (fun j => hterm j) (hw.subtype _)
    _ = (1 / α) * ∑' j : ℤ, (if j ∈ Finset.Icc (⌊resampCentre s t k⌋ - m)
          (⌊resampCentre s t k⌋ + m) then 0 else
          gauss (π * α⁻¹ ^ 2) (-(resampCentre s t k) + j)) := by
        congr 1
        rw [tsum_subtype ((truncWindow s t m k : Set ℤ))ᶜ
          (fun j : ℤ => gauss (π * α⁻¹ ^ 2) (-(resampCentre s t k) + j))]
        refine tsum_congr fun j => ?_
        unfold truncWindow
        by_cases hj : j ∈ Finset.Icc (⌊resampCentre s t k⌋ - m) (⌊resampCentre s t k⌋ + m)
        · rw [Set.indicator_of_notMem (by simpa using hj)]
          simp only [hj, ↓reduceIte]
        · rw [Set.indicator_of_mem (by simpa using hj)]
          simp only [hj, ↓reduceIte]
    _ ≤ (1 / α) * (2 * ∑' n : ℕ, gauss (π * α⁻¹ ^ 2) (m + n)) :=
        mul_le_mul_of_nonneg_left (tsum_outside_window_le hc _ m) (by positivity)
    _ = (2 / α) * ∑' n : ℕ, gauss (π * α⁻¹ ^ 2) (m + n) := by ring

/-- Under the paper's constraints the Gaussian tail beyond `m` is below `(7/6) 2^(-p)`. -/
theorem gauss_tail_small (hα : 0 < α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) :
    ∑' n : ℕ, gauss (π * α⁻¹ ^ 2) (m + n) ≤ (7 / 6) / 2 ^ p := by
  set c := π * α⁻¹ ^ 2 with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨K, rfl⟩ : ∃ K, m = K + 1 := ⟨m - 1, by omega⟩
  have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  refine le_trans (gauss_tail_le hc K) ?_
  rw [← hcast]
  set mr : ℝ := ((K + 1 : ℕ) : ℝ) with hmr
  have hmr0 : 0 ≤ mr := Nat.cast_nonneg _
  have hα2 : 0 < α ^ 2 := by positivity
  -- `m ≥ α²`, hence `c m ≥ π`.
  have hm_ge : α ^ 2 ≤ mr := by
    by_contra h
    push Not at h
    have h1 : mr * mr < α ^ 2 * α ^ 2 := mul_lt_mul'' h h hmr0 hmr0
    have h2 : α ^ 2 * α ^ 2 ≤ (p : ℝ) * α ^ 2 := mul_le_mul_of_nonneg_right hαp hα2.le
    nlinarith
  have hcm : π ≤ c * mr := by
    rw [hc_def]
    have h1 : α⁻¹ ^ 2 * α ^ 2 ≤ α⁻¹ ^ 2 * mr := mul_le_mul_of_nonneg_left hm_ge (by positivity)
    have h2 : α⁻¹ ^ 2 * α ^ 2 = 1 := by field_simp
    have h3 : π * (α⁻¹ ^ 2 * α ^ 2) ≤ π * (α⁻¹ ^ 2 * mr) :=
      mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    rw [h2, mul_one] at h3
    linarith
  -- The Gaussian value `exp(-c m²) ≤ exp(-π p) ≤ 2^(-p)`.
  have hgauss : gauss c mr ≤ 1 / 2 ^ p := by
    unfold gauss
    have hcm2 : π * p ≤ c * mr ^ 2 := by
      rw [hc_def]
      have h1 : π * α⁻¹ ^ 2 * (p * α ^ 2) ≤ π * α⁻¹ ^ 2 * mr ^ 2 :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have h2 : π * α⁻¹ ^ 2 * (p * α ^ 2) = π * p := by field_simp
      linarith
    have hexp : Real.exp (-c * mr ^ 2) ≤ Real.exp (-π) ^ p := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      linarith
    have hpi : Real.exp (-π) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 1 ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
      linarith
    calc Real.exp (-c * mr ^ 2) ≤ Real.exp (-π) ^ p := hexp
      _ ≤ (1 / 2) ^ p := pow_le_pow_left₀ (Real.exp_pos _).le hpi p
      _ = 1 / 2 ^ p := by rw [one_div_pow]
  -- The geometric denominator is at least `6/7`.
  have hden : 6 / 7 ≤ 1 - Real.exp (-c * (2 * K + 3)) := by
    have h1 : -c * (2 * K + 3) ≤ -6 := by
      have h0 : 2 * mr ≤ 2 * (K : ℝ) + 3 := by rw [hmr]; push_cast; linarith
      have h2 : c * (2 * mr) ≤ c * (2 * (K : ℝ) + 3) := mul_le_mul_of_nonneg_left h0 hc.le
      linarith [Real.pi_gt_three]
    have h2 : Real.exp (-c * (2 * K + 3)) ≤ 1 / 7 := by
      calc Real.exp (-c * (2 * K + 3)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr h1
        _ ≤ 1 / 7 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
          linarith [Real.add_one_le_exp (6 : ℝ)]
    linarith
  have hden0 : 0 < 1 - Real.exp (-c * (2 * K + 3)) := by linarith
  rw [div_le_iff₀ hden0]
  calc gauss c mr ≤ 1 / 2 ^ p := hgauss
    _ = (7 / 6) / 2 ^ p * (6 / 7) := by ring
    _ ≤ (7 / 6) / 2 ^ p * (1 - Real.exp (-c * (2 * K + 3))) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- The truncation error is below `3 / (α 2^p)` under the paper's constraints. -/
theorem resampS_trunc_err_pow (hα : 0 < α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (u : ZMod s → ℂ)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : ZMod t) :
    ‖resampS s t α u k - resampSTrunc s t α m u k‖ ≤ 3 / (α * 2 ^ p) := by
  refine le_trans (resampS_trunc_err hα u hu m k) ?_
  have h := gauss_tail_small hα hαp hm hm1
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  calc (2 / α) * ∑' n : ℕ, gauss (π * α⁻¹ ^ 2) (m + n)
      ≤ (2 / α) * ((7 / 6) / 2 ^ p) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (7 / 3) / (α * 2 ^ p) := by field_simp; norm_num
    _ ≤ 3 / (α * 2 ^ p) := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- A finite sum of approximated terms accumulates at most the sum of the errors. -/
theorem trunc_sum_err {ι : Type*} (I : Finset ι) (z' z : ι → ℂ) {p : ℕ} {c : ℝ}
    (hz : ∀ j ∈ I, 2 ^ p * ‖z' j - z j‖ ≤ c) :
    2 ^ p * ‖∑ j ∈ I, z' j - ∑ j ∈ I, z j‖ ≤ c * I.card := by
  rw [← Finset.sum_sub_distrib]
  calc (2 : ℝ) ^ p * ‖∑ j ∈ I, (z' j - z j)‖
      ≤ 2 ^ p * ∑ j ∈ I, ‖z' j - z j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ I, 2 ^ p * ‖z' j - z j‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ I, c := Finset.sum_le_sum hz
    _ = c * I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Lemma 4.9: a fixed-point evaluation of the truncated series, with per-term
scaled error at most `c`, approximates `S u` with scaled error `c (2m+1) + 3`. -/
theorem resampS_approx_err (hα : 1 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (u : ZMod s → ℂ)
    (hu : ∀ j, ‖u j‖ ≤ 1) (k : ZMod t) (z' : ℤ → ℂ) {c : ℝ}
    (hz : ∀ j ∈ truncWindow s t m k, 2 ^ p * ‖z' j - (1 / α : ℂ) *
      ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j)‖ ≤ c) :
    2 ^ p * ‖(∑ j ∈ truncWindow s t m k, z' j) - resampS s t α u k‖ ≤ c * (2 * m + 1) + 3 := by
  have hα0 : 0 < α := by linarith
  have htrunc := resampS_trunc_err_pow hα0 hαp hm hm1 u hu k
  have hsum := trunc_sum_err (truncWindow s t m k) z'
    (fun j => (1 / α : ℂ) *
      ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j)) hz
  rw [card_truncWindow] at hsum
  have hT : ∑ j ∈ truncWindow s t m k, (1 / α : ℂ) *
      ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℂ) * u j) =
      resampSTrunc s t α m u k := by
    unfold resampSTrunc
    rw [Finset.mul_sum]
  rw [hT] at hsum
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have htr : (2 : ℝ) ^ p * ‖resampSTrunc s t α m u k - resampS s t α u k‖ ≤ 3 := by
    rw [norm_sub_rev]
    calc (2 : ℝ) ^ p * ‖resampS s t α u k - resampSTrunc s t α m u k‖
        ≤ 2 ^ p * (3 / (α * 2 ^ p)) := mul_le_mul_of_nonneg_left htrunc h2p.le
      _ = 3 / α := by field_simp
      _ ≤ 3 := by rw [div_le_iff₀ hα0]; linarith
  calc (2 : ℝ) ^ p * ‖(∑ j ∈ truncWindow s t m k, z' j) - resampS s t α u k‖
      = 2 ^ p * ‖((∑ j ∈ truncWindow s t m k, z' j) - resampSTrunc s t α m u k) +
          (resampSTrunc s t α m u k - resampS s t α u k)‖ := by congr 2; ring
    _ ≤ 2 ^ p * (‖(∑ j ∈ truncWindow s t m k, z' j) - resampSTrunc s t α m u k‖ +
          ‖resampSTrunc s t α m u k - resampS s t α u k‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) h2p.le
    _ = 2 ^ p * ‖(∑ j ∈ truncWindow s t m k, z' j) - resampSTrunc s t α m u k‖ +
          2 ^ p * ‖resampSTrunc s t α m u k - resampS s t α u k‖ := by ring
    _ ≤ c * ((2 * m + 1 : ℕ) : ℝ) + 3 := add_le_add hsum htr
    _ = c * (2 * m + 1) + 3 := by push_cast; ring

end IntegerMultBounds.NLogN
