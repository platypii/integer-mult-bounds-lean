import IntegerMultBounds.NLogN.ExpEval
import IntegerMultBounds.NLogN.SmallMultiplierCost

/-! The weight-evaluation cost of the main algorithm with a concrete
multiplication cost. The plain FFT multiplier's a priori bound is enclosed in
the monotone, superadditive envelope `Mcost₀ q = 10^6 q (log₂ q + 1)²`, and the
binary-splitting evaluation of `e^(−z)` to `q` bits with exponent at most
`4 q² + 4` (the application's exponents are at most `π m²/α² ≤ 4 p²` for the
window `m ≤ 2 p`) then costs at most `2 · 10^11 · q (log₂ q + 1)³` word
operations for `q ≥ 16`, hence `K₀ q (log₂ q)^4`, the shape the joint cost
recurrence consumes. Only `q ≥ 16` is covered; the recurrence applies the bound
at `q = precision n ≥ 24576`. -/

namespace IntegerMultBounds.NLogN

/-- A monotone, superadditive envelope of the plain FFT multiplier's bit cost. -/
def Mcost₀ (q : ℕ) : ℕ := 10 ^ 6 * q * (Nat.log 2 q + 1) ^ 2

theorem smallMulBits_le_envelope {q : ℕ} (hq : 2 ≤ q) : smallMulBits q ≤ Mcost₀ q := by
  unfold Mcost₀
  calc smallMulBits q ≤ 10 ^ 6 * q * Nat.log 2 q ^ 2 := smallMulBits_le hq
    _ ≤ 10 ^ 6 * q * (Nat.log 2 q + 1) ^ 2 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (by omega) 2

theorem Mcost₀_mono : Monotone Mcost₀ := by
  intro a b hab
  unfold Mcost₀
  have hl : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right hab
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left _ hab
  · exact Nat.pow_le_pow_left (by omega) 2

theorem Mcost₀_superadd (a b : ℕ) : Mcost₀ a + Mcost₀ b ≤ Mcost₀ (a + b) := by
  unfold Mcost₀
  have ha : Nat.log 2 a ≤ Nat.log 2 (a + b) := Nat.log_mono_right (by omega)
  have hb : Nat.log 2 b ≤ Nat.log 2 (a + b) := Nat.log_mono_right (by omega)
  have ha' : (Nat.log 2 a + 1) ^ 2 ≤ (Nat.log 2 (a + b) + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hb' : (Nat.log 2 b + 1) ^ 2 ≤ (Nat.log 2 (a + b) + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  generalize (Nat.log 2 a + 1) ^ 2 = ca at *
  generalize (Nat.log 2 b + 1) ^ 2 = cb at *
  generalize (Nat.log 2 (a + b) + 1) ^ 2 = c at *
  nlinarith

/-- The evaluation cost of one Gaussian weight to `q` bits, exponent at most
`4 q² + 4`, using the enveloped plain multiplier for every product. -/
def expCost (q : ℕ) : ℕ :=
  expOps Mcost₀ q (termCount q) (Nat.log 2 (termCount q) + 2) (4 * q ^ 2 + 4)

theorem log_eighty_mul_le (q : ℕ) : Nat.log 2 (80 * q) ≤ Nat.log 2 q + 7 := by
  set L := Nat.log 2 q with hL
  have hpL : q < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have : 80 * q < 2 ^ (L + 8) := by
    calc 80 * q < 80 * 2 ^ (L + 1) := by omega
      _ ≤ 128 * 2 ^ (L + 1) := by omega
      _ = 2 ^ (L + 8) := by ring
  have := Nat.log_lt_of_lt_pow' (by omega) this
  omega

theorem expCost_le {q : ℕ} (hq : 16 ≤ q) :
    expCost q ≤ 2 * 10 ^ 11 * q * (Nat.log 2 q + 1) ^ 3 := by
  have h := expOps_quasi Mcost₀ Mcost₀_superadd Mcost₀_mono q (4 * q ^ 2 + 4) hq le_rfl
  unfold expCost
  refine le_trans h ?_
  set L := Nat.log 2 q with hL
  have hL4 : 4 ≤ L := log_ge_four q hq
  have h80 : Nat.log 2 (80 * q) ≤ L + 7 := log_eighty_mul_le q
  have hM80 : Mcost₀ (80 * q) ≤ 10 ^ 6 * (80 * q) * (L + 8) ^ 2 := by
    unfold Mcost₀
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 2
  have hMq : Mcost₀ q = 10 ^ 6 * q * (L + 1) ^ 2 := rfl
  have h1 : (L + 3) * (L + 8) ^ 2 ≤ 192 * (L + 1) ^ 3 := by nlinarith
  have h2 : (4 * L + 9) * (L + 1) ^ 2 ≤ 9 * (L + 1) ^ 3 := by nlinarith
  have h3 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  calc 164 * q + 8 * (L + 3) * Mcost₀ (80 * q) + (4 * L + 9) * Mcost₀ q
      ≤ 164 * q + 8 * (L + 3) * (10 ^ 6 * (80 * q) * (L + 8) ^ 2)
          + (4 * L + 9) * (10 ^ 6 * q * (L + 1) ^ 2) := by
        rw [hMq]
        have := Nat.mul_le_mul_left (8 * (L + 3)) hM80
        omega
    _ = 164 * q + 64 * 10 ^ 7 * q * ((L + 3) * (L + 8) ^ 2)
          + 10 ^ 6 * q * ((4 * L + 9) * (L + 1) ^ 2) := by ring
    _ ≤ 164 * q * (L + 1) ^ 3 + 64 * 10 ^ 7 * q * (192 * (L + 1) ^ 3)
          + 10 ^ 6 * q * (9 * (L + 1) ^ 3) := by
        have e1 := Nat.mul_le_mul_left (64 * 10 ^ 7 * q) h1
        have e2 := Nat.mul_le_mul_left (10 ^ 6 * q) h2
        have e3 : 164 * q ≤ 164 * q * (L + 1) ^ 3 := Nat.le_mul_of_pos_right _ h3
        omega
    _ ≤ 2 * 10 ^ 11 * q * (L + 1) ^ 3 := by nlinarith

theorem expCost_le_log4 {q : ℕ} (hq : 16 ≤ q) :
    expCost q ≤ 16 * 10 ^ 11 * q * Nat.log 2 q ^ 4 := by
  have h := expCost_le hq
  have hL4 : 4 ≤ Nat.log 2 q := log_ge_four q hq
  have h3 : (Nat.log 2 q + 1) ^ 3 ≤ 8 * Nat.log 2 q ^ 4 := by
    have : Nat.log 2 q + 1 ≤ 2 * Nat.log 2 q := by omega
    calc (Nat.log 2 q + 1) ^ 3 ≤ (2 * Nat.log 2 q) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * Nat.log 2 q ^ 3 := by ring
      _ ≤ 8 * Nat.log 2 q ^ 4 := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by omega) (by norm_num)
  calc expCost q ≤ 2 * 10 ^ 11 * q * (Nat.log 2 q + 1) ^ 3 := h
    _ ≤ 2 * 10 ^ 11 * q * (8 * Nat.log 2 q ^ 4) := Nat.mul_le_mul_left _ h3
    _ = 16 * 10 ^ 11 * q * Nat.log 2 q ^ 4 := by ring

/-- The weight-evaluation cost hypothesis of the joint recurrence, discharged. -/
theorem exists_exp_cost :
    ∃ K₀ : ℕ, ∀ q, 16 ≤ q → expCost q ≤ K₀ * q * Nat.log 2 q ^ 4 :=
  ⟨16 * 10 ^ 11, fun _ hq => expCost_le_log4 hq⟩

theorem Mcost₀_le_cube {q : ℕ} (hq : 2 ≤ q) : Mcost₀ q ≤ 4 * 10 ^ 6 * q * Nat.log 2 q ^ 3 := by
  have hl : 1 ≤ Nat.log 2 q := Nat.log_pos (by norm_num) hq
  unfold Mcost₀
  have h2 : (Nat.log 2 q + 1) ^ 2 ≤ 4 * Nat.log 2 q ^ 3 := by
    have : Nat.log 2 q + 1 ≤ 2 * Nat.log 2 q := by omega
    calc (Nat.log 2 q + 1) ^ 2 ≤ (2 * Nat.log 2 q) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * Nat.log 2 q ^ 2 := by ring
      _ ≤ 4 * Nat.log 2 q ^ 3 := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by omega) (by norm_num)
  calc 10 ^ 6 * q * (Nat.log 2 q + 1) ^ 2 ≤ 10 ^ 6 * q * (4 * Nat.log 2 q ^ 3) :=
        Nat.mul_le_mul_left _ h2
    _ = 4 * 10 ^ 6 * q * Nat.log 2 q ^ 3 := by ring

/-- The small-multiplier cost hypothesis of the joint recurrence, for the envelope. -/
theorem exists_small_mult_cost' :
    ∃ K₁ : ℕ, ∀ q, 2 ≤ q → Mcost₀ q ≤ K₁ * q * Nat.log 2 q ^ 3 :=
  ⟨4 * 10 ^ 6, fun _ hq => Mcost₀_le_cube hq⟩

end IntegerMultBounds.NLogN
