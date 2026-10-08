import IntegerMultBounds.Swap.Recurrence

/-! The cost assembly of the arbitrary-width interchange (§4, Lemma 4.4). Binary
chunks of width `u` are padded to the radix width `e ≤ u`; the top `ρ` digits
form a row field of range `q^(2ρ) ≥ W^k`; the remaining width `e - ρ` is split
into base-`m` pieces handled by power-width calls on less than twice the
volume; the high-digit moves, padding, descriptors, and cleanup cost a fixed
multiple of `ρ + log (2e) + 1` per unit volume. The total is `O(u^τ)` per unit
volume with a constant independent of `u`. The field-order bookkeeping of the
construction is a tape obligation. -/

namespace IntegerMultBounds.Swap.ArbitraryWidth

open Finset Recurrence

/-- A logarithm is uniformly below a multiple of any positive power on `[1, ∞)`. -/
theorem log_le_mul_rpow {τ : ℝ} (hτ : 0 < τ) {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ≤ 1 / τ * u ^ τ := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ u) hτ
  rw [div_eq_mul_one_div, mul_comm] at h
  exact h

section Shape
variable (m W q₀ : ℕ)

/-- The radix-`(q₀ + 2)` width covering binary chunks of width `u`. -/
def width (u : ℕ) : ℕ := radixWidth q₀ u

theorem width_le (u : ℕ) : width q₀ u ≤ u := radixWidth_le q₀ u

theorem one_le_width {u : ℕ} (hu : 1 ≤ u) : 1 ≤ width q₀ u := by
  by_contra h
  push Not at h
  have h0 : width q₀ u = 0 := by omega
  have hspec := radixWidth_spec q₀ u
  unfold width at h0
  rw [h0, pow_zero] at hspec
  have : 2 ≤ 2 ^ u := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu
  omega

/-- The number of high digits forming the row field. -/
noncomputable def rowDigits (u : ℕ) : ℕ :=
  ⌈(⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) * Real.log W / (2 * Real.log ((q₀ : ℝ) + 2))⌉₊

/-- The remaining width, split into base-`m` pieces. -/
noncomputable def rest (u : ℕ) : ℕ := width q₀ u - rowDigits m W q₀ u

/-- The row field has range at least `W^k` for the piece exponent `k`. -/
theorem row_field (hW : 1 ≤ W) (u : ℕ) :
    W ^ ⌈Real.log (width q₀ u) / Real.log m⌉₊ ≤ (q₀ + 2) ^ (2 * rowDigits m W q₀ u) := by
  unfold rowDigits
  have := row_range (W := W) (q := q₀ + 2) hW (by omega) ⌈Real.log (width q₀ u) / Real.log m⌉₊
  push_cast at this ⊢
  exact this

/-- Per-volume cost of the power-width calls on the pieces: constant `K₀`, on
less than twice the volume. -/
noncomputable def pieceCost (K₀ τ : ℝ) (u : ℕ) : ℝ :=
  2 * K₀ * ∑ j ∈ range (Nat.log m (rest m W q₀ u) + 1),
    ((rest m W q₀ u / m ^ j % m : ℕ) : ℝ) * ((m ^ j : ℕ) : ℝ) ^ τ

/-- Per-volume cost of the high-digit moves, padding, descriptors, and cleanup. -/
noncomputable def overhead (A : ℝ) (u : ℕ) : ℝ :=
  A * ((rowDigits m W q₀ u : ℝ) + Real.log (2 * width q₀ u) + 1)

theorem rowDigits_le (hm : 2 ≤ m) (hW : 1 ≤ W) {u : ℕ} (hu : 1 ≤ u) :
    (rowDigits m W q₀ u : ℝ) ≤
      Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) / Real.log m * Real.log u +
        Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) + 1 := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hq0 : (0 : ℝ) ≤ q₀ := by positivity
  have hlogq : 0 < Real.log ((q₀ : ℝ) + 2) := Real.log_pos (by linarith)
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  have hc0 : 0 ≤ Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) := div_nonneg hlogW (by linarith)
  have he1 : (1 : ℝ) ≤ width q₀ u := by exact_mod_cast one_le_width q₀ hu
  have heu : (width q₀ u : ℝ) ≤ u := by exact_mod_cast width_le q₀ u
  have hloge : 0 ≤ Real.log (width q₀ u) := Real.log_nonneg he1
  have hlogeu : Real.log (width q₀ u) ≤ Real.log u :=
    (Real.log_le_log_iff (by linarith) (by linarith)).mpr heu
  have hk : (⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) <
      Real.log (width q₀ u) / Real.log m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk0 : (0 : ℝ) ≤ ⌈Real.log (width q₀ u) / Real.log m⌉₊ := Nat.cast_nonneg _
  have hceil : (rowDigits m W q₀ u : ℝ) <
      (⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) * Real.log W /
        (2 * Real.log ((q₀ : ℝ) + 2)) + 1 := by
    unfold rowDigits
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hk0 hlogW) (by linarith))
  have heq : (⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) * Real.log W /
      (2 * Real.log ((q₀ : ℝ) + 2)) =
      (⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) *
        (Real.log W / (2 * Real.log ((q₀ : ℝ) + 2))) := by ring
  rw [heq] at hceil
  have h1 : (⌈Real.log (width q₀ u) / Real.log m⌉₊ : ℝ) *
      (Real.log W / (2 * Real.log ((q₀ : ℝ) + 2))) ≤
      (Real.log u / Real.log m + 1) * (Real.log W / (2 * Real.log ((q₀ : ℝ) + 2))) := by
    apply mul_le_mul_of_nonneg_right _ hc0
    have := div_le_div_of_nonneg_right hlogeu hlogm.le
    linarith
  have h2 : (Real.log u / Real.log m + 1) * (Real.log W / (2 * Real.log ((q₀ : ℝ) + 2))) =
      Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) / Real.log m * Real.log u +
        Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) := by ring
  linarith

theorem pieceCost_le (hm : 2 ≤ m) {τ : ℝ} (hτ : 0 < τ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) {u : ℕ}
    (hu : 1 ≤ u) :
    pieceCost m W q₀ K₀ τ u ≤
      2 * K₀ * (((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1)) * (u : ℝ) ^ τ := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 1 < (m : ℝ) ^ τ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < m by omega)) hτ
  have hK₁ : 0 ≤ ((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) :=
    div_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
  unfold pieceCost
  rcases Nat.eq_zero_or_pos (rest m W q₀ u) with h0 | hpos
  · rw [h0]
    simp only [Nat.zero_div, Nat.zero_mod, Nat.cast_zero, zero_mul, sum_const_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hK₁) (by positivity)
  · have hn : rest m W q₀ u ≤ u := le_trans (Nat.sub_le _ _) (width_le q₀ u)
    have hk : m ^ Nat.log m (rest m W q₀ u) ≤ rest m W q₀ u := Nat.pow_log_le_self m hpos.ne'
    have hsum := pieces_le hm hτ (fun j => rest m W q₀ u / m ^ j % m)
      (fun j => base_digit_lt hm _ j) hk
    have hrpow : ((rest m W q₀ u : ℕ) : ℝ) ^ τ ≤ (u : ℝ) ^ τ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) hτ.le
    calc 2 * K₀ * ∑ j ∈ range (Nat.log m (rest m W q₀ u) + 1),
          ((rest m W q₀ u / m ^ j % m : ℕ) : ℝ) * ((m ^ j : ℕ) : ℝ) ^ τ
        ≤ 2 * K₀ * (((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) *
            ((rest m W q₀ u : ℕ) : ℝ) ^ τ) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 * K₀ * (((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) * (u : ℝ) ^ τ) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hK₁) (by positivity)
      _ = _ := by ring

/-- Lemma 4.4's cost: the arbitrary-width interchange costs `O(u^τ)` per unit
volume, with a constant independent of `u`. -/
theorem cost (hm : 2 ≤ m) (hW : 1 ≤ W) {τ : ℝ} (hτ : 0 < τ) {A K₀ : ℝ} (hA : 0 ≤ A)
    (hK₀ : 0 ≤ K₀) (total : ℕ → ℝ)
    (htotal : ∀ u, 1 ≤ u → total u ≤ overhead m W q₀ A u + pieceCost m W q₀ K₀ τ u) :
    ∃ K : ℝ, ∀ u : ℕ, 1 ≤ u → total u ≤ K * (u : ℝ) ^ τ := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hq0 : (0 : ℝ) ≤ q₀ := by positivity
  have hlogq : 0 < Real.log ((q₀ : ℝ) + 2) := Real.log_pos (by linarith)
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  set c := Real.log W / (2 * Real.log ((q₀ : ℝ) + 2)) with hc
  have hc0 : 0 ≤ c := div_nonneg hlogW (by linarith)
  have hcL : 0 ≤ c / Real.log m := div_nonneg hc0 hlogm.le
  have hx : 1 < (m : ℝ) ^ τ :=
    Real.one_lt_rpow (by exact_mod_cast (show 1 < m by omega)) hτ
  set K₁ := ((m : ℝ) - 1) * (m : ℝ) ^ τ / ((m : ℝ) ^ τ - 1) with hK₁def
  have hK₁ : 0 ≤ K₁ := div_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨A * ((c / Real.log m + 1) * (1 / τ) + c + 2 + Real.log 2) + 2 * K₀ * K₁, ?_⟩
  intro u hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hupow : 1 ≤ (u : ℝ) ^ τ := Real.one_le_rpow hu1 hτ.le
  have hlogu : Real.log u ≤ 1 / τ * (u : ℝ) ^ τ := log_le_mul_rpow hτ hu1
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hρ := rowDigits_le m W q₀ hm hW hu
  have he1 : (1 : ℝ) ≤ width q₀ u := by exact_mod_cast one_le_width q₀ hu
  have heu : (width q₀ u : ℝ) ≤ u := by exact_mod_cast width_le q₀ u
  have hlog2e : Real.log (2 * (width q₀ u : ℝ)) ≤ Real.log 2 + Real.log u := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have := (Real.log_le_log_iff (by linarith) (by linarith)).mpr heu
    linarith
  have hpiece := pieceCost_le m W q₀ hm hτ hK₀ hu
  have hover : overhead m W q₀ A u ≤
      A * ((c / Real.log m + 1) * (1 / τ) + c + 2 + Real.log 2) * (u : ℝ) ^ τ := by
    unfold overhead
    have h1 : (rowDigits m W q₀ u : ℝ) + Real.log (2 * (width q₀ u : ℝ)) + 1 ≤
        (c / Real.log m + 1) * Real.log u + (c + 2 + Real.log 2) := by
      rw [hc]
      linarith
    have h2 : (c / Real.log m + 1) * Real.log u ≤
        (c / Real.log m + 1) * (1 / τ) * (u : ℝ) ^ τ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlogu (by linarith)
    have h3 : c + 2 + Real.log 2 ≤ (c + 2 + Real.log 2) * (u : ℝ) ^ τ :=
      le_mul_of_one_le_right (by linarith) hupow
    calc A * ((rowDigits m W q₀ u : ℝ) + Real.log (2 * (width q₀ u : ℝ)) + 1)
        ≤ A * ((c / Real.log m + 1) * (1 / τ) * (u : ℝ) ^ τ +
            (c + 2 + Real.log 2) * (u : ℝ) ^ τ) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
      _ = A * ((c / Real.log m + 1) * (1 / τ) + c + 2 + Real.log 2) * (u : ℝ) ^ τ := by ring
  calc total u ≤ overhead m W q₀ A u + pieceCost m W q₀ K₀ τ u := htotal u hu
    _ ≤ A * ((c / Real.log m + 1) * (1 / τ) + c + 2 + Real.log 2) * (u : ℝ) ^ τ +
        2 * K₀ * K₁ * (u : ℝ) ^ τ := by
        rw [hK₁def]
        linarith
    _ = _ := by ring

end Shape

end IntegerMultBounds.Swap.ArbitraryWidth
