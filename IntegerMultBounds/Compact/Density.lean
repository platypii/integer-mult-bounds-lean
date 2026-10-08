import IntegerMultBounds.Compact.Counting
import IntegerMultBounds.Compact.RepairBounds

/-! Fractions of actual exceptional packed addresses. Exact finite counts are
converted to the source's union bounds, then to its uniform numerical estimate.
This file counts records; extracting and sorting them on tapes remains separate. -/

namespace IntegerMultBounds.Compact

noncomputable def badFraction {α : Type*} (P : α → Prop) : ℝ :=
  (Nat.card {x // ¬P x} : ℝ) / (Nat.card α : ℝ)

theorem badFraction_eq {α : Type*} [Fintype α] (P : α → Prop)
    (hpos : 0 < (Nat.card α : ℝ)) :
    badFraction P = 1 - (Nat.card {x // P x} : ℝ) / (Nat.card α : ℝ) := by
  classical
  have hle : Nat.card {x // P x} ≤ Nat.card α := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le P
  have hc : Nat.card {x // ¬P x} = Nat.card α - Nat.card {x // P x} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [badFraction, hc, Nat.cast_sub hle, sub_div, div_self (ne_of_gt hpos)]

theorem badFraction_le_one {α : Type*} [Fintype α] (P : α → Prop)
    (hpos : 0 < (Nat.card α : ℝ)) : badFraction P ≤ 1 := by
  rw [badFraction_eq P hpos]
  have : 0 ≤ (Nat.card {x // P x} : ℝ) / (Nat.card α : ℝ) := by positivity
  linarith

private theorem toNat_real (z : ℤ) (hz : 0 ≤ z) : (z.toNat : ℝ) = (z : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hz

theorem early_total_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    (Nat.card (EarlyAddress B L n) : ℝ) = (2 * (L : ℝ)) ^ n * (B : ℝ) ^ n := by
  rw [card_earlyAddress, Nat.cast_mul,
    toNat_real _ (pow_nonneg (by omega) n), toNat_real _ (pow_nonneg hB.le n)]
  push_cast
  rfl

theorem early_good_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    (Nat.card {x : EarlyAddress B L n // earlyGood B L n x} : ℝ) =
      (2 * (L : ℝ) - 8 * (B : ℝ)) ^ n * ((B : ℝ) - 1) ^ n := by
  rw [card_earlyGood B L hB hL, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    toNat_real _ (by omega), toNat_real _ (by omega)]
  push_cast
  rfl

theorem late_total_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    (Nat.card (LateAddress B L n) : ℝ) =
      (B : ℝ) ^ n * ((2 * (L : ℝ)) ^ n * (B : ℝ) ^ n) := by
  rw [Nat.card_prod, Nat.cast_mul, card_field,
    toNat_real _ (pow_nonneg hB.le n), early_total_real B L hB hL]
  push_cast
  rfl

theorem late_good_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    (Nat.card {x : LateAddress B L n // lateGood B L n x} : ℝ) =
      ((B : ℝ) - 1) ^ n *
        ((2 * (L : ℝ) - 8 * (B : ℝ)) ^ n * ((B : ℝ) - 1) ^ n) := by
  rw [Nat.card_congr (lateGoodEquiv B L n), Nat.card_prod, Nat.cast_mul,
    card_restricted_field B hB, card_unsaturated_digit, Nat.cast_pow,
    toNat_real _ (by omega), early_good_real B L hB hL hguard]
  push_cast
  rfl

theorem early_fraction_eq (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (earlyGood B L n) =
      1 - ((2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) ^ n *
        (((B : ℝ) - 1) / (B : ℝ)) ^ n := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [badFraction_eq _ (by rw [early_total_real B L hB hL]; positivity),
    early_total_real B L hB hL, early_good_real B L hB hL hguard,
    mul_div_mul_comm, ← div_pow, ← div_pow]

theorem late_fraction_eq (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (lateGood B L n) =
      1 - (((B : ℝ) - 1) / (B : ℝ)) ^ n *
        (((2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) ^ n *
          (((B : ℝ) - 1) / (B : ℝ)) ^ n) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [badFraction_eq _ (by rw [late_total_real B L hB hL]; positivity),
    late_total_real B L hB hL, late_good_real B L hB hL hguard,
    mul_div_mul_comm, mul_div_mul_comm, ← div_pow, ← div_pow]

private theorem one_sub_mul_le (x y : ℝ) (hx : x ≤ 1) (hy : y ≤ 1) :
    1 - x * y ≤ (1 - x) + (1 - y) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

private theorem one_sub_pow_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  have h := one_add_mul_sub_le_pow (show -1 ≤ x by linarith) n
  linarith

private theorem digit_fractions (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) :
    (0 ≤ (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ)) ∧
      (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ)) ≤ 1) ∧
    (0 ≤ ((B : ℝ) - 1) / (B : ℝ) ∧ ((B : ℝ) - 1) / (B : ℝ) ≤ 1) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hgr : 4 * (B : ℝ) ≤ L := by exact_mod_cast hguard
  constructor
  · exact ⟨div_nonneg (by linarith) (by positivity),
      (div_le_one (by positivity)).mpr (by linarith)⟩
  · exact ⟨div_nonneg (by linarith) hBr.le, (div_le_one hBr).mpr (by linarith)⟩

/-- One temporary block and one guarded target block. -/
theorem early_bad_fraction_le (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (earlyGood B L n) ≤ (n : ℝ) / B + 8 * n * B / (2 * L) := by
  obtain ⟨⟨hu₀, hu₁⟩, ⟨hv₀, hv₁⟩⟩ := digit_fractions B L hB hL hguard
  have hprod := one_sub_mul_le _ _ (pow_le_one₀ hu₀ hu₁ (n := n))
    (pow_le_one₀ hv₀ hv₁ (n := n))
  have hu := one_sub_pow_le _ hu₀ n
  have hv := one_sub_pow_le _ hv₀ n
  rw [early_fraction_eq B L hB hL hguard]
  calc
    _ ≤ n * (1 - (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) +
        n * (1 - ((B : ℝ) - 1) / (B : ℝ)) := by linarith
    _ = _ := by
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
      field_simp
      ring

/-- Two temporary blocks and one guarded target block. -/
theorem late_bad_fraction_le (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (lateGood B L n) ≤ 2 * (n : ℝ) / B + 8 * n * B / (2 * L) := by
  obtain ⟨⟨hu₀, hu₁⟩, ⟨hv₀, hv₁⟩⟩ := digit_fractions B L hB hL hguard
  have hun := pow_le_one₀ hu₀ hu₁ (n := n)
  have hvn := pow_le_one₀ hv₀ hv₁ (n := n)
  have hprod := one_sub_mul_le _ _ hun hvn
  have hmul := (mul_le_mul_of_nonneg_right hun (pow_nonneg hv₀ n)).trans
    (by simpa only [one_mul] using hvn)
  have hprod' := one_sub_mul_le _ _ hvn hmul
  have hu := one_sub_pow_le _ hu₀ n
  have hv := one_sub_pow_le _ hv₀ n
  rw [late_fraction_eq B L hB hL hguard]
  calc
    _ ≤ n * (1 - (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) +
        2 * n * (1 - ((B : ℝ) - 1) / (B : ℝ)) := by linarith
    _ = _ := by
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
      field_simp
      ring

/-- The common source bound, capped by one, for the actual two bad-address
predicates. Here `B * C` is the complete target-digit range `2 * L`. -/
theorem common_bad_fraction_le (B L C : ℤ) (hB : 0 < B) (hC : 8 ≤ C)
    (hwidth : 2 * L = B * C) (n : ℕ) :
    badFraction (earlyGood B L n) ≤ min 1 (2 * (n : ℝ) / B + 8 * n / C) ∧
    badFraction (lateGood B L n) ≤ min 1 (2 * (n : ℝ) / B + 8 * n / C) := by
  have hL : 0 < L := by nlinarith
  have hguard : 4 * B ≤ L := by nlinarith
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hCr : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hw : 2 * (L : ℝ) = (B : ℝ) * C := by exact_mod_cast hwidth
  have hcancel : 8 * (n : ℝ) * B / (2 * L) = 8 * n / C := by
    rw [hw]
    field_simp
  have he := early_bad_fraction_le B L hB hL hguard n
  have hl := late_bad_fraction_le B L hB hL hguard n
  rw [hcancel] at he hl
  constructor
  · apply le_min
    · exact badFraction_le_one _ (by rw [early_total_real B L hB hL]; positivity)
    · have hnonneg : (0 : ℝ) ≤ n / B := by positivity
      simp only [mul_div_assoc] at he ⊢
      linarith
  · exact le_min
      (badFraction_le_one _ (by rw [late_total_real B L hB hL]; positivity)) hl

/-- Uniform density for the actual repair predicates, from the radix sizes
used in the complexity argument. This no longer assumes a bad-set fraction. -/
theorem actual_repair_density (B L C : ℤ) (n : ℕ) (p : ℝ)
    (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) (hB : 0 < B)
    (hwidth : 2 * L = B * C)
    (hBsize : 64 * p ^ 4 ≤ (B : ℝ)) (hCsize : 1024 * p ^ 4 ≤ (C : ℝ)) :
    badFraction (earlyGood B L n) ≤ min 1 (5 / (128 * p ^ 3)) ∧
    badFraction (lateGood B L n) ≤ min 1 (5 / (128 * p ^ 3)) := by
  have hp4 : 1 ≤ p ^ 4 := one_le_pow₀ hp
  have hCr : (8 : ℝ) ≤ C := by linarith
  have hC : 8 ≤ C := by exact_mod_cast hCr
  have hc := common_bad_fraction_le B L C hB hC hwidth n
  have hd := repair_density_bound p n B C (by linarith) (by positivity) hn hBsize hCsize
  exact ⟨hc.1.trans (min_le_min_left 1 hd), hc.2.trans (min_le_min_left 1 hd)⟩

/-- The manuscript's dyadic cutoff gives the density bound for both concrete
packed-repair address spaces. The segment range is exactly `2 ^ K`. -/
theorem dyadic_actual_repair_density (p : ℝ) (n ell K : ℕ)
    (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) (hell : p ≤ (2 : ℝ) ^ ell)
    (hK : 8 * ell + 16 ≤ K) :
    badFraction (earlyGood ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n) ≤
        min 1 (5 / (128 * p ^ 3)) ∧
    badFraction (lateGood ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n) ≤
        min 1 (5 / (128 * p ^ 3)) := by
  obtain ⟨hB, hC⟩ := dyadic_repair_radices p ell K (by linarith) hell hK
  have hwidth : (2 : ℤ) * 2 ^ (K - 1) =
      2 ^ (4 * ell + 6) * 2 ^ (K - (4 * ell + 6)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  exact actual_repair_density _ _ ((2 : ℤ) ^ (K - (4 * ell + 6))) n p hp hn
    (by positivity) hwidth
    (by simpa only [Int.cast_pow, Int.cast_ofNat] using hB)
    (by simpa only [Int.cast_pow, Int.cast_ofNat] using hC)

end IntegerMultBounds.Compact
