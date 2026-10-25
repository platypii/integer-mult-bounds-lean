module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLogGrowth
public import IntegerMultBounds.MathlibTM2.Fast.RingProd

/-! # Packed logarithms at the chirp caller's polynomial precision scale -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host

/-- A quadratic packed size has only a constant multiple of the precision's binary digits. -/
theorem chirp_size_quadratic {p N A : ℕ} (hp : 1 ≤ p) (hN : N ≤ A * p ^ 2) :
    Nat.size N + 1 ≤ (Nat.size A + 3) * (Nat.log 2 p + 1) := by
  let L := Nat.log 2 p + 1
  have hpL : p < 2 ^ L := Nat.lt_pow_succ_log_self (by decide) p
  have hpow : N < 2 ^ (Nat.size A + 2 * L) := by
    calc
      N ≤ A * p ^ 2 := hN
      _ < 2 ^ Nat.size A * p ^ 2 :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self A) (by positivity)
      _ ≤ 2 ^ Nat.size A * (2 ^ L) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpL.le 2)
      _ = 2 ^ (Nat.size A + 2 * L) := by
        conv_rhs => rw [pow_add, Nat.mul_comm 2 L, pow_mul]
  have hs : Nat.size N ≤ Nat.size A + 2 * L := Nat.size_le.mpr hpow
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hA : Nat.size A ≤ Nat.size A * L := Nat.le_mul_of_pos_right _ hL
  change Nat.size N + 1 ≤ (Nat.size A + 3) * L
  nlinarith only [hs, hL, hA]

/-- Reuse the supplier's cube-size lemma; its outer digit count is at most linear in its input. -/
theorem chirp_size_cube_factor (N : ℕ) :
    Nat.size (Nat.size N ^ 3) + 1 ≤ 3 * (Nat.size N + 1) := by
  have hcube := size_cube_le (Nat.size N)
  have hsize : Nat.size (Nat.size N) ≤ Nat.size N := Nat.size_le.mpr Nat.lt_two_pow_self
  change Nat.size (Nat.size N ^ 3) ≤ 3 * Nat.size (Nat.size N) at hcube
  omega

/-- The two packed-size logarithms fit the original precision's p^(1/128) allowance. -/
theorem chirp_packed_log_factors_le (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p N : ℕ, 1 ≤ p → N ≤ A * p ^ 2 →
      (((Nat.size N + 1) * (Nat.size (Nat.size N ^ 3) + 1) : ℕ) : ℝ) ≤
        C * (p : ℝ) ^ (1 / 128 : ℝ) := by
  refine ⟨3 * ((Nat.size A + 3 : ℕ) : ℝ) ^ 2 * 262144, by positivity, ?_⟩
  intro p N hp hN
  have hs := chirp_size_quadratic hp hN
  have hc := chirp_size_cube_factor N
  have hf : (Nat.size N + 1) * (Nat.size (Nat.size N ^ 3) + 1) ≤
      3 * (Nat.size A + 3) ^ 2 * (Nat.log 2 p + 1) ^ 2 := by
    calc
      _ ≤ ((Nat.size A + 3) * (Nat.log 2 p + 1)) *
          (3 * ((Nat.size A + 3) * (Nat.log 2 p + 1))) :=
        Nat.mul_le_mul hs (hc.trans (Nat.mul_le_mul_left 3 hs))
      _ = _ := by ring
  have hlog := compact_natLog_succ_le hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog2 : (((Nat.log 2 p + 1 : ℕ) : ℝ)) ^ 2 ≤
      262144 * (p : ℝ) ^ (1 / 128 : ℝ) := by
    calc
      _ ≤ (512 * (p : ℝ) ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hlog 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (1 / 256 : ℝ)), ← Real.rpow_mul hp0.le]
        norm_num
  have hf' : (((Nat.size N + 1) * (Nat.size (Nat.size N ^ 3) + 1) : ℕ) : ℝ) ≤
      3 * ((Nat.size A + 3 : ℕ) : ℝ) ^ 2 * ((Nat.log 2 p + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hf
  calc
    _ ≤ _ := hf'
    _ ≤ 3 * ((Nat.size A + 3 : ℕ) : ℝ) ^ 2 * (262144 * (p : ℝ) ^ (1 / 128 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = _ := by ring

/-- A packed product with O(m*p) bits and polynomial packed size costs O(m*M(p)). -/
theorem chirp_ringBound_le (A B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p m N : ℕ, 1 ≤ p → 1 ≤ m →
      N ≤ B * m * p → N ≤ A * p ^ 2 →
      (rpRingBound N : ℝ) ≤ C * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨L, hL, hlog⟩ := chirp_packed_log_factors_le A
  let c : ℝ := (costC cA cB cC0 : ℕ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  refine ⟨4 * c * (B + 1) * L + 11000 * B + 250000, by positivity, ?_⟩
  intro p m N hp hm hN hquad
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (1 : ℝ) ≤ (m : ℝ) * p := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hN' : (N : ℝ) ≤ (B : ℝ) * m * p := by exact_mod_cast hN
  have hN1 : (N : ℝ) + 1 ≤ ((B : ℝ) + 1) * m * p := by nlinarith only [hN', hmp]
  have hpow : (p : ℝ) * (p : ℝ) ^ (1 / 128 : ℝ) = (p : ℝ) ^ (129 / 128 : ℝ) := by
    rw [show (129 / 128 : ℝ) = 1 + 1 / 128 by norm_num, Real.rpow_add hp0, Real.rpow_one]
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) := by
    rw [← hpow]
    exact le_mul_of_one_le_right hp0.le (Real.one_le_rpow hp1 (by norm_num))
  let F : ℝ := (((Nat.size N + 1) * (Nat.size (Nat.size N ^ 3) + 1) : ℕ) : ℝ)
  have hF : F ≤ L * (p : ℝ) ^ (1 / 128 : ℝ) := hlog p N hp hquad
  have hpacked : 4 * c * ((N : ℝ) + 1) * F ≤
      (4 * c * ((B : ℝ) + 1) * L) * m * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ (4 * c * (((B : ℝ) + 1) * m * p)) * (L * (p : ℝ) ^ (1 / 128 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hN1 (by positivity)) hF (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← hpow]; ring
  have hlinear : 11000 * (N : ℝ) + 250000 ≤
      (11000 * (B : ℝ) + 250000) * m * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ (11000 * (B : ℝ) + 250000) * m * p := by nlinarith only [hN', hmp]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by positivity)
  have hcast (K : ℕ) :
      ((4 * K * (N + 1) * (Nat.size N + 1) * (Nat.size (Nat.size N ^ 3) + 1) +
        11000 * N + 250000 : ℕ) : ℝ) =
      4 * (K : ℝ) * ((N : ℝ) + 1) * F + 11000 * (N : ℝ) + 250000 := by
    dsimp only [F]
    push_cast
    ring
  change ((4 * costC cA cB cC0 * (N + 1) * (Nat.size N + 1) *
    (Nat.size (Nat.size N ^ 3) + 1) + 11000 * N + 250000 : ℕ) : ℝ) ≤ _
  rw [hcast]
  calc
    _ ≤ (4 * c * ((B : ℝ) + 1) * L) * m * (p : ℝ) ^ (129 / 128 : ℝ) +
        (11000 * (B : ℝ) + 250000) * m * (p : ℝ) ^ (129 / 128 : ℝ) := by
      simpa only [c, add_assoc] using add_le_add hpacked hlinear
    _ = _ := by ring

/-- Pointwise products at any fixed linear working width satisfy the same multiplier allowance. -/
theorem chirp_rmul_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p w : ℕ, 1 ≤ p → 1 ≤ w → w ≤ cw * p →
      (rmulCost w : ℝ) ≤ C * (p : ℝ) ^ (129 / 128 : ℝ) := by
  let K : ℝ := (ssMulConst : ℕ)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  refine ⟨2 * K * 262144 * (cw : ℝ) ^ (129 / 128 : ℝ) + 160 * cw + 128, by positivity, ?_⟩
  intro p w hp hw hwidth
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hOne : (1 : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) :=
    Real.one_le_rpow hp1 (by norm_num)
  have hwidth' : (w : ℝ) ≤ (cw : ℝ) * p := by exact_mod_cast hwidth
  have hlog : (mLogLog w : ℝ) ≤
      (262144 * (cw : ℝ) ^ (129 / 128 : ℝ)) * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ 262144 * (w : ℝ) ^ (129 / 128 : ℝ) := compact_mLogLog_le hw
      _ ≤ 262144 * ((cw : ℝ) * p) ^ (129 / 128 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hwidth' (by norm_num)) (by norm_num)
      _ = _ := by rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; ring
  have hwPow : (w : ℝ) ≤ (cw : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) :=
    hwidth'.trans (mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg _))
  have hMult := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * K by positivity)
  have hLin := mul_le_mul_of_nonneg_left hwPow (show (0 : ℝ) ≤ 160 by norm_num)
  have hConst := mul_le_mul_of_nonneg_left hOne (show (0 : ℝ) ≤ 128 by norm_num)
  have hcast (S : ℕ) : ((2 * (S * mLogLog w) + 160 * w + 128 : ℕ) : ℝ) =
      2 * (S : ℝ) * (mLogLog w : ℝ) + 160 * (w : ℝ) + 128 := by push_cast; ring
  change ((2 * (ssMulConst * mLogLog w) + 160 * w + 128 : ℕ) : ℝ) ≤ _
  rw [hcast]
  calc
    _ ≤ (2 * K) * ((262144 * (cw : ℝ) ^ (129 / 128 : ℝ)) * (p : ℝ) ^ (129 / 128 : ℝ)) +
        160 * ((cw : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)) + 128 * (p : ℝ) ^ (129 / 128 : ℝ) := by
      simpa only [K, mul_one] using add_le_add (add_le_add hMult hLin) hConst
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
