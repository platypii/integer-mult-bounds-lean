module

public import IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Layer.SelectedMoments

/-- At exponent one the selected bit profile can pay at most 35 additional unit-rank
children per invocation across the nine stages and 32 replicas. -/
theorem bit_extra_rank_budget (k : ℕ) :
    (bitHistogram.map (fun e => e.1 * e.2)).sum + 9 * 32 * k < 64 * 28416 ↔ k ≤ 35 := by
  change 1808352 + 288 * k < 1818624 ↔ k ≤ 35
  omega

/-- Charging the endpoint swap separately on both address halves at every port
costs 222 unit children per invocation. Even at exponent one, such a schedule
needs to save at least 53,665 units of rank elsewhere in the single-class profile. -/
theorem bit_separate_port_swap_budget (saved : ℕ) :
    (bitHistogram.map (fun e => e.1 * e.2)).sum + 9 * 32 * 111 * 2 <
      64 * 28416 + saved ↔ 53665 ≤ saved := by
  change 1808352 + 63936 < 1818624 + saved ↔ 53665 ≤ saved
  omega

/-- At a primitive saving of one thousandth, even splitting every selected
child into rank-one children leaves room for nine more per stage and replica.
The bill includes the increased bad-residue surcharge on all split calls. -/
theorem bit_split_budget (n : ℕ)
    (hn : n ≤ (bitHistogram.map (fun e => e.1 * e.2)).sum + 9 * 32 * 9) :
    histMoment [(1, n)] 64 (1 - 1 / 1000) + surcharge [(1, n)] 64 (1 - 1 / 1000) < 28416 := by
  change n ≤ 1810944 at hn
  have cert : 64 ^ 1 * 10 ^ (6 * 1000) ≤ 1004168 ^ 1000 * 1 ^ 1 := by decide +kernel
  have power := child_power_le (r := 1) (m := 64) (p := 1) (q := 1000) (D := 6)
    Nat.one_pos (by decide) (by decide) cert
  have bad := surcharge_le [(1, n)] (m := 64) (p := 1) (q := 1000) (D := 6)
    (by decide) (by decide) cert
  have nr : (n : ℝ) ≤ 1810944 := by exact_mod_cast hn
  simp only [histMoment, callCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul] at bad power ⊢
  linarith only [bad, nr, mul_le_mul_of_nonneg_left power (Nat.cast_nonneg n)]

private def lowerOk (e : ℕ × ℕ × ℕ) : Bool :=
  decide (0 < e.1 ∧ 0 < e.2.2 - 1 ∧
    e.1 ^ 10 * (e.2.2 - 1) ^ 5769 ≤ 64 ^ 10 * (10 ^ 10) ^ 5769)

private theorem lower_checked : bitCertificate.all lowerOk = true := by decide +kernel

private theorem lower_moment (rows : List (ℕ × ℕ × ℕ)) (ok : rows.all lowerOk = true) :
    ((rows.map fun e => e.2.1 * e.1 * (e.2.2 - 1)).sum : ℕ) / (64 * 10 ^ 10 : ℝ) ≤
      histMoment (rows.map fun e => (e.1, e.2.1)) 64 (1 - bitSaving) := by
  induction rows with
  | nil => simp [histMoment]
  | cons e rows ih =>
    simp only [List.all_cons, Bool.and_eq_true, lowerOk, decide_eq_true_eq] at ok
    obtain ⟨⟨hr, hu, check⟩, rest⟩ := ok
    let u := e.2.2 - 1
    have pos : (0 : ℝ) < u := by exact_mod_cast hu
    have base : (0 : ℝ) < e.1 / 64 := by positivity
    have powBound : ((e.1 : ℝ) / 64) ^ bitSaving ≤ 10 ^ 10 / (u : ℝ) := by
      rw [bitSaving_eq]
      apply rpow_div_le (by positivity) (by positivity) (by decide)
      rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have cast := (Nat.cast_le (α := ℝ)).mpr (check.trans_eq (Nat.mul_comm _ _))
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, u] using cast
    have power := div_le_div_of_nonneg_left base.le (Real.rpow_pos_of_pos base _) powBound
    simp only [histMoment, List.map_cons, List.sum_cons, Nat.cast_add, add_div]
    apply add_le_add _ (ih rest)
    push_cast
    calc _ = (e.2.1 : ℝ) * ((e.1 / 64) / (10 ^ 10 / (u : ℝ))) := by
            simp only [u, div_div_eq_mul_div]; ring
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg e.2.1)
           simpa only [Real.rpow_sub base, Real.rpow_one] using power

/-- Even one additional rank-one child in the entire single-class profile exceeds
the budget at the selected exponent, before the bad-residue surcharge. -/
theorem bit_one_extra_child_over_budget :
    28416 < histMoment bitHistogram 64 (1 - bitSaving) + (1 / 64 : ℝ) ^ (1 - bitSaving) := by
  have h := lower_moment bitCertificate lower_checked
  rw [bitCertificate_histogram] at h
  have extra : (1 / 64 : ℝ) ≤ (1 / 64 : ℝ) ^ (1 - bitSaving) := by
    nth_rw 1 [← Real.rpow_one (1 / 64 : ℝ)]
    apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    norm_num [bitSaving]
  apply lt_of_lt_of_le _ (add_le_add h extra)
  norm_num [bitCertificate]

end IntegerMultBounds.MathlibTM2.M6
