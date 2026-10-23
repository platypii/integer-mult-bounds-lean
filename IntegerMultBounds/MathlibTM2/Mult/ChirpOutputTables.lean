module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTables
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputValue

/-! # Computed factors for the chirp output arithmetic

Generate E at q-Γ bits and interpret its numerator at q bits. The normalization
factor is the natural quotient of 2^q by 2α, with a proved fixed-point error.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Resampling

def chirpNormalization (q α : ℕ) : ℕ := 2 ^ q / (2 * α)

theorem chirpNormalization_le (q α : ℕ) : chirpNormalization q α ≤ 2 ^ q :=
  Nat.div_le_self _ _

/-- Normalization needs only natural division, and errs by at most one grid unit. -/
theorem chirpNormalization_err (q α : ℕ) (hα : 0 < α) :
    |(chirpNormalization q α : ℝ) / 2 ^ q - 1 / (2 * (α : ℝ))| ≤ 1 / (2 : ℝ) ^ q := by
  have hb : (0 : ℤ) < 2 * (α : ℤ) := by positivity
  have hdiv := WeightTable.fdiv_err ((2 : ℤ) ^ q) (2 * (α : ℤ)) hb
  have heq : ((2 : ℤ) ^ q / (2 * (α : ℤ))) = (chirpNormalization q α : ℤ) := by
    simp [chirpNormalization, Int.natCast_ediv]
  rw [heq] at hdiv
  have h : |(chirpNormalization q α : ℝ) - 2 ^ q * (1 / (2 * (α : ℝ)))| ≤ 1 := by
    simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, div_eq_mul_inv, one_mul] using hdiv
  exact normalize_error (by positivity) h

/-- The output machine uses the generated E numerator directly at precision q. -/
theorem chirpOutputE_err (s t α q Γ b : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hgate : Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1) :
    |(chirpTableE s t α (q - Γ) b : ℝ) / 2 ^ q -
      NLogN.chirpE s t (α : ℝ) b / 2 ^ Γ| ≤ 2 / (2 : ℝ) ^ (q - Γ) := by
  simpa only [Nat.sub_add_cancel hΓq] using chirpTableE_err s t α (q - Γ) Γ b hs hst hα hq hgate

/-- The computed normalization factor has absolute value at most one. -/
theorem chirpNormalization_abs_le_one (q α : ℕ) :
    |(chirpNormalization q α : ℝ) / 2 ^ q| ≤ 1 := by
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ q)).mpr
  exact_mod_cast chirpNormalization_le q α

/-- The generated normalized E factor is small enough for the output word envelope. -/
theorem chirpOutputE_abs_le_two (s t α q Γ b : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hgate : Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hΓ : NLogN.chirpE s t (α : ℝ) b ≤ 2 ^ Γ) :
    |(chirpTableE s t α (q - Γ) b : ℝ) / 2 ^ q| ≤ 2 := by
  have he := chirpOutputE_err s t α q Γ b hs hst hα hΓq hq hgate
  have hη := chirpTable_eta_le (q - Γ) hq
  have hb : NLogN.chirpE s t (α : ℝ) b / 2 ^ Γ ≤ 1 :=
    (div_le_one (by positivity : (0 : ℝ) < 2 ^ Γ)).mpr hΓ
  rw [abs_of_nonneg (by positivity)]
  have hu := (abs_le.mp he).2
  linarith

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
