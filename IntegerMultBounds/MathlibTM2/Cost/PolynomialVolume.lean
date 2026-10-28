module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase

/-! Polynomial setup bounds below the selected whole-box volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- **A polynomial in `b` times a power of `r` is eventually below `T`.** `T = 2^(log₂ T - ℓ) r`
with `2 m ℓ ≤ log₂ T - ℓ` once `d ≥ 2m + 2`, and `b ≤ 4 (log₂ T - ℓ)`. -/
theorem ml_poly_r_le_T (A k m : ℕ) : ∀ᶠ n in atTop, A * b n ^ k * r n ^ m ≤ T n := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (eventually_mul_pow_le_two_pow (A * 8 ^ k) k)
  filter_upwards [eventually_big, tendsto_b.eventually_ge_atTop (8 * M₀),
    tendsto_d.eventually_ge_atTop (2 * m + 2)] with n h hb hd
  obtain ⟨hT, hm⟩ := mt_T_split h
  have hdℓ := dℓ_lt h.one_le_d
  have hd8 := h.eight_d_le_b
  have hbL := h.logT_bounds.1
  have hℓ : ℓ n ≤ logT n := mt_ℓ_le_logT h
  have h1 : (2 * m + 2) * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hd
  have e : (2 * m + 2) * ℓ n = 2 * (m * ℓ n) + 2 * ℓ n := by ring
  have h2m : m * ℓ n ≤ logT n - ℓ n := by omega
  obtain ⟨u, hu⟩ : ∃ u, u = logT n - ℓ n - m * ℓ n := ⟨_, rfl⟩
  have hu1 : logT n - ℓ n = u + m * ℓ n := by omega
  have hbu : b n ≤ 8 * u := by omega
  have huM : M₀ ≤ u := by omega
  have hA : A * b n ^ k ≤ 2 ^ u := by
    calc A * b n ^ k ≤ A * (8 * u) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbu k)
      _ = A * 8 ^ k * u ^ k := by rw [mul_pow]; ring
      _ ≤ 2 ^ u := hM₀ u huM
  have hr : r n ^ m = 2 ^ (m * ℓ n) := by unfold r; rw [← pow_mul, Nat.mul_comm]
  rw [hT, hu1, pow_add, hr]
  calc A * b n ^ k * 2 ^ (m * ℓ n) ≤ 2 ^ u * 2 ^ (m * ℓ n) := Nat.mul_le_mul_right _ hA
    _ ≤ 2 ^ u * 2 ^ (m * ℓ n) * r n := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow

end IntegerMultBounds.MathlibTM2.Cost
