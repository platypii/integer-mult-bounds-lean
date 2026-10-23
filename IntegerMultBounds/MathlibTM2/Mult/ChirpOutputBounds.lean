module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputTables
public import IntegerMultBounds.MathlibTM2.Fast.CMul

/-! # Signed word bounds for chirp output arithmetic -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- A decoded norm bound controls both signed numerator components. -/
theorem fits_of_norm_value_bound {q w : ℕ} (x : GaussianInt) (B : ℝ)
    (hB : ‖value q x‖ ≤ B) (hw : (2 : ℝ) ^ q * B < 2 ^ (w - 1)) : Fits w x := by
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hre : |(x.re : ℝ)| < 2 ^ (w - 1) := by
    have h := (Complex.abs_re_le_norm (value q x)).trans hB
    change |(x.re : ℝ) / 2 ^ q| ≤ B at h
    rw [abs_div, abs_of_pos hp] at h
    exact ((div_le_iff₀ hp).mp h).trans_lt (by simpa only [mul_comm] using hw)
  have him : |(x.im : ℝ)| < 2 ^ (w - 1) := by
    have h := (Complex.abs_im_le_norm (value q x)).trans hB
    change |(x.im : ℝ) / 2 ^ q| ≤ B at h
    rw [abs_div, abs_of_pos hp] at h
    exact ((div_le_iff₀ hp).mp h).trans_lt (by simpa only [mul_comm] using hw)
  constructor
  · exact_mod_cast hre
  · exact_mod_cast him

/-- One real truncated product increases the decoded norm by at most the factor norm. -/
theorem norm_value_real_product (q : ℕ) (x : GaussianInt) (e : ℤ) (B C : ℝ)
    (hx : ‖value q x‖ ≤ B) (he : |(e : ℝ) / 2 ^ q| ≤ C) (hC : 0 ≤ C) :
    ‖value q (tdivN q ((⟨e, 0⟩ : GaussianInt) * x))‖ ≤ C * B := by
  rw [value_tdivN_mul, value_real]
  apply (norm_rhoC_le q _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul he hx (norm_nonneg _) hC

/-- The first output shift has decoded norm at most the correlation scale. -/
theorem norm_chirpScaledCorrelation (q l : ℕ) (c : GaussianInt)
    (hc : ‖value (q + 1) c‖ ≤ 1) :
    ‖value q ((2 : GaussianInt) ^ (l + 1) * c)‖ ≤ 4 * (2 : ℝ) ^ l := by
  rw [value_chirp_correlation_scale, norm_mul]
  have hn : ‖(4 * (2 ^ l : ℕ) : ℂ)‖ = 4 * (2 : ℝ) ^ l := by
    push_cast
    simp only [norm_mul, norm_pow, Complex.norm_ofNat]
  rw [hn]
  exact mul_le_of_le_one_right (by positivity) hc

theorem chirpScaledCorrelation_fits (q l w : ℕ) (c : GaussianInt)
    (hc : ‖value (q + 1) c‖ ≤ 1) (hw : q + l + 4 ≤ w) :
    Fits w ((2 : GaussianInt) ^ (l + 1) * c) := by
  apply fits_of_norm_value_bound _ _ (norm_chirpScaledCorrelation q l c hc)
  have hpow : (2 : ℝ) ^ (q + l + 2) < 2 ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  calc
    (2 : ℝ) ^ q * (4 * 2 ^ l) = 2 ^ (q + l + 2) := by simp only [pow_add]; ring
    _ < _ := hpow

/-- A real factor of absolute value at most two fits with three guard bits. -/
theorem chirpRealFactor_fits (q w : ℕ) (e : ℤ)
    (he : |(e : ℝ) / 2 ^ q| ≤ 2) (hw : q + 3 ≤ w) : Fits w (⟨e, 0⟩ : GaussianInt) := by
  apply fits_of_norm_value_bound _ 2
  · rw [value_real, Complex.norm_real, Real.norm_eq_abs]
    exact he
  · have hpow : (2 : ℝ) ^ (q + 1) < 2 ^ (w - 1) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    simpa only [pow_succ] using hpow

/-- Both post-correlation products and the Γ shift obey a uniform bound. -/
theorem norm_chirpOutputNumerator (q l Γ : ℕ) (c : GaussianInt) (e a : ℤ)
    (hc : ‖value (q + 1) c‖ ≤ 1)
    (he : |(e : ℝ) / 2 ^ q| ≤ 2) (ha : |(a : ℝ) / 2 ^ q| ≤ 1) :
    ‖value q (chirpOutputNumerator q l Γ c e a)‖ ≤ 8 * (2 : ℝ) ^ (l + Γ) := by
  have hscale := norm_chirpScaledCorrelation q l c hc
  have hprod := norm_value_real_product q ((2 : GaussianInt) ^ (l + 1) * c) e _ _
    hscale he (by norm_num)
  have hshift : ‖value q ((2 : GaussianInt) ^ Γ *
      tdivN q ((⟨e, 0⟩ : GaussianInt) * ((2 : GaussianInt) ^ (l + 1) * c)))‖ ≤
      (2 : ℝ) ^ Γ * (2 * (4 * (2 : ℝ) ^ l)) := by
    rw [value_pow_two_mul, norm_mul, norm_pow]
    simpa only [Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 ^ Γ)
  have hout := norm_value_real_product q _ a _ _ hshift ha (by norm_num)
  change ‖value q (chirpOutputNumerator q l Γ c e a)‖ ≤ _ at hout
  calc _ ≤ 1 * ((2 : ℝ) ^ Γ * (2 * (4 * (2 : ℝ) ^ l))) := hout
    _ = 8 * (2 : ℝ) ^ (l + Γ) := by rw [pow_add]; ring

/-- A simple guard-bit envelope prevents signed aliasing of the final q-grid numerator. -/
theorem chirpOutputNumerator_fits (q l Γ w : ℕ) (c : GaussianInt) (e a : ℤ)
    (hc : ‖value (q + 1) c‖ ≤ 1) (he : |(e : ℝ) / 2 ^ q| ≤ 2)
    (ha : |(a : ℝ) / 2 ^ q| ≤ 1) (hw : q + l + Γ + 5 ≤ w) :
    Fits w (chirpOutputNumerator q l Γ c e a) := by
  apply fits_of_norm_value_bound _ _ (norm_chirpOutputNumerator q l Γ c e a hc he ha)
  have hpow : (2 : ℝ) ^ (q + l + Γ + 3) < 2 ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  calc
    (2 : ℝ) ^ q * (8 * 2 ^ (l + Γ)) = 2 ^ (q + l + Γ + 3) := by
      simp only [pow_add]
      ring
    _ < _ := hpow

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
