module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableArgs

/-! # Computable chirp table numerators and their grid errors

The numerators use the existing Taylor/Machin evaluator in natural arithmetic. The output
factor is interpreted at precision `q+Γ`, so dividing the growing factor by `2^Γ` introduces
no additional rounding. Tape execution of the evaluator is supplied separately.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Resampling

/-- Natural input-factor table numerator at precision `q`. -/
def chirpTableG (s t α q m k0 a : ℕ) : ℕ :=
  WeightNat.expPiNat true q (chirpGN s t m k0 a) (chirpKD t α)

/-- Natural shifted-kernel table numerator at precision `q`. -/
def chirpTableK (s t α q m k0 : ℕ) (a : ℤ) : ℕ :=
  WeightNat.expPiNat true q (chirpKN s t m k0 a) (chirpKD t α)

/-- Growing-factor numerator; interpret at precision `q+Γ` for the normalized output factor. -/
def chirpTableE (s t α q b : ℕ) : ℕ :=
  WeightNat.expPiNat false q (chirpEN s t b) (chirpED t α)

/-- Normalizing a fixed-scale error divides the error by that positive scale. -/
theorem normalize_error {x y c ε : ℝ} (hc : 0 < c) (h : |x - c * y| ≤ ε) :
    |x / c - y| ≤ ε / c := by
  have he : x / c - y = (x - c * y) / c := by field_simp
  rw [he, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right h hc.le

theorem expPiNat_neg_err (q a b : ℕ) (hq : 13 ≤ q) (hb : 0 < b) :
    |(WeightNat.expPiNat true q a b : ℝ) / 2 ^ q - Real.exp (-(Real.pi * a / b))| ≤
      (3 / 2 : ℝ) / 2 ^ q := by
  have h := WeightTable.expPi_neg_err q a b hq hb
  rw [WeightNat.expPi_eq_nat true q a b hq] at h
  simp only [Int.cast_natCast] at h
  exact normalize_error (by positivity) h

theorem expPiNat_pos_err (q a b : ℕ) (hq : 13 ≤ q) (hb : 0 < b)
    (hx : Real.pi * a / b ≤ q - 1) :
    |(WeightNat.expPiNat false q a b : ℝ) / 2 ^ q - Real.exp (Real.pi * a / b)| ≤
      (3 / 2 : ℝ) / 2 ^ q := by
  have h := WeightTable.expPi_pos_err q a b hq hb hx
  rw [WeightNat.expPi_eq_nat false q a b hq] at h
  simp only [Int.cast_natCast] at h
  exact normalize_error (by positivity) h

/-- Certified input-factor table accuracy for the common chirp error budget. -/
theorem chirpTableG_err (s t α q m k0 a : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hq : 13 ≤ q) :
    |(chirpTableG s t α q m k0 a : ℝ) / 2 ^ q - chirpG s t (α : ℝ) m k0 a| ≤
      2 / (2 : ℝ) ^ q := by
  have ht : 0 < t := by omega
  rw [chirpG_eq_expPi s t α m k0 a hs hst hα]
  exact (expPiNat_neg_err q _ _ hq (by unfold chirpKD; positivity)).trans
    (div_le_div_of_nonneg_right (by norm_num) (by positivity))

/-- Certified kernel table accuracy on signed shifts. -/
theorem chirpTableK_err (s t α q m k0 : ℕ) (a : ℤ) (hs : 0 < s) (ht : 0 < t)
    (hα : 0 < α) (hq : 13 ≤ q) :
    |(chirpTableK s t α q m k0 a : ℝ) / 2 ^ q - chirpK s t (α : ℝ) m k0 a| ≤
      2 / (2 : ℝ) ^ q := by
  rw [chirpK_eq_expPi s t α m k0 a hs ht hα]
  exact (expPiNat_neg_err q _ _ hq (by unfold chirpKD; positivity)).trans
    (div_le_div_of_nonneg_right (by norm_num) (by positivity))

/-- Certified output-factor table accuracy after normalization by `2^Γ`. -/
theorem chirpTableE_err (s t α q Γ b : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hq : 13 ≤ q)
    (hx : Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ q - 1) :
    |(chirpTableE s t α q b : ℝ) / 2 ^ (q + Γ) - chirpE s t (α : ℝ) b / 2 ^ Γ| ≤
      2 / (2 : ℝ) ^ q := by
  have ht : 0 < t := by omega
  have h := expPiNat_pos_err q (chirpEN s t b) (chirpED t α) hq (by unfold chirpED; positivity) hx
  rw [← chirpE_eq_expPi s t α b hs hst hα] at h
  have hΓ : (1 : ℝ) ≤ 2 ^ Γ := by exact one_le_pow₀ (by norm_num)
  calc
    _ = |(chirpTableE s t α q b : ℝ) / 2 ^ q - chirpE s t (α : ℝ) b| / 2 ^ Γ := by
      rw [pow_add, ← div_div, ← sub_div, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Γ)]
    _ ≤ ((3 / 2 : ℝ) / 2 ^ q) / 2 ^ Γ := div_le_div_of_nonneg_right h (by positivity)
    _ ≤ (3 / 2 : ℝ) / 2 ^ q := div_le_self (by positivity) hΓ
    _ ≤ 2 / (2 : ℝ) ^ q := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- The common table/rounding error budget already meets the analytic `η ≤ 1/4` gate. -/
theorem chirpTable_eta_le (q : ℕ) (hq : 13 ≤ q) : 2 / (2 : ℝ) ^ q ≤ 1 / 4 := by
  have hpow : (8 : ℝ) ≤ 2 ^ q := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ q by omega))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ q)).2
  linarith

/-- The computed tables and the standard truncation rounding produce unit-disk ring records. -/
theorem chirpTable_records_norm {s t : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (α q m : ℕ) (hα : 0 < α) (hq : 13 ≤ q)
    (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1) (n i : ℕ) :
    ‖chirpRecIn (t := t) m (rhoC q)
      (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q) u n i‖ ≤ 1 ∧
    ‖chirpRecK m (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q) n i‖ ≤ 1 := by
  have hs : 0 < s := NeZero.pos s
  have ht : 0 < t := NeZero.pos t
  apply norm_chirpRec_le (α := (α : ℝ)) hst m (rhoC q) (2 / (2 : ℝ) ^ q)
    (norm_rhoC_sub_le_two q) ((chirpTable_eta_le q hq).trans (by norm_num))
    (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
    (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
    (fun k0 a => chirpTableG_err s t α q m k0 a hs hst hα hq)
    (fun k0 a => chirpTableK_err s t α q m k0 a hs ht hα hq) u hu n i

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
