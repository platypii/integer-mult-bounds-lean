import IntegerMultBounds.TimeBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Input and transform sizes (§8). From `b = lg n` the algorithm sets
`p = 6b`, `d = ⌊b^ε⌋`, `K = ⌊d^c⌋`, a power of two `T` in `[4n/b, 8n/b)`,
`ℓ = ⌈log₂ T / d⌉`, and `r = 2^ℓ`. This file proves the comparison bounds the
layer and transform interfaces use: `24 n ≤ T p < 48 n`, `p^ε / 12 ≤ d ≤ p^ε`,
`p^(εc) / 24 ≤ K ≤ p^(εc)`, `b / 2 ≤ log₂ T ≤ b`, and `p / (12 d) ≤ ℓ ≤ p / (3 d)`,
all for sufficiently large `n`, with the fixed constants of the manuscript.
The exponent `c` is the witness parameter `spacing`. -/

namespace IntegerMultBounds.Sizes

open Filter Parameters Machine TimeBound

/-- `b = lg n`. -/
def b (n : ℕ) : ℕ := lg n

theorem one_le_b (n : ℕ) : 1 ≤ b n := one_le_lg n

theorem precision_eq (n : ℕ) : precision n = 6 * (b n : ℝ) := rfl

/-- For `n ≥ 2`, `b` is the ceiling logarithm and `2^(b-1) < n ≤ 2^b`. -/
theorem b_eq_clog {n : ℕ} (hn : 2 ≤ n) : b n = Nat.clog 2 n := by
  unfold b lg
  apply max_eq_left
  by_contra h
  push Not at h
  have h0 : Nat.clog 2 n = 0 := by omega
  have := Nat.le_pow_clog (by norm_num : 1 < 2) n
  rw [h0, pow_zero] at this
  omega

theorem le_two_pow_b (n : ℕ) : n ≤ 2 ^ b n := by
  calc n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
    _ ≤ 2 ^ b n := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)

theorem two_pow_b_pred_lt {n : ℕ} (hn : 2 ≤ n) : 2 ^ (b n - 1) < n := by
  rw [b_eq_clog hn]
  exact Nat.pow_pred_clog_lt_self (by norm_num) (by omega)

theorem b_le_self {n : ℕ} (hn : 1 ≤ n) : b n ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    decide
  · rw [b_eq_clog h]
    have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < n)
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : Nat.clog 2 n - 1 < 2 ^ (Nat.clog 2 n - 1) :=
      Nat.lt_two_pow_self
    omega

theorem tendsto_b : Tendsto (fun n => (b n : ℝ)) atTop atTop := by
  have := tendsto_precision
  unfold precision at this
  have h := this.atTop_div_const (by norm_num : (0 : ℝ) < 6)
  refine h.congr fun n => ?_
  show 6 * (lg n : ℝ) / 6 = (b n : ℝ)
  unfold b
  field_simp

section Dimension

/-- The number of axes `d = ⌊b^ε⌋`. -/
noncomputable def d (n : ℕ) : ℕ := ⌊(b n : ℝ) ^ epsilon⌋₊

theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]
theorem epsilon_le_one : epsilon ≤ 1 := by norm_num [epsilon]

theorem one_le_d (n : ℕ) : 1 ≤ d n := by
  unfold d
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.floor_pos]
  exact Real.one_le_rpow (by exact_mod_cast one_le_b n) epsilon_pos.le

/-- `d ≤ b^ε ≤ p^ε`. -/
theorem d_le (n : ℕ) : (d n : ℝ) ≤ precision n ^ epsilon := by
  unfold d
  have hb : (1 : ℝ) ≤ b n := by exact_mod_cast one_le_b n
  calc (⌊(b n : ℝ) ^ epsilon⌋₊ : ℝ) ≤ (b n : ℝ) ^ epsilon := Nat.floor_le (by positivity)
    _ ≤ precision n ^ epsilon := by
        rw [precision_eq]
        exact Real.rpow_le_rpow (by positivity) (by linarith) epsilon_pos.le

theorem d_le_b (n : ℕ) : d n ≤ b n := by
  unfold d
  have hb : (1 : ℝ) ≤ b n := by exact_mod_cast one_le_b n
  have : (b n : ℝ) ^ epsilon ≤ (b n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb epsilon_le_one
  rw [Real.rpow_one] at this
  exact_mod_cast (Nat.floor_le (by positivity : (0 : ℝ) ≤ (b n : ℝ) ^ epsilon)).trans this

/-- Eventually `b^ε ≥ 2`, so that the floor loses at most half. -/
theorem eventually_two_le_rpow : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (b n : ℝ) ^ epsilon := by
  have h : Tendsto (fun n => (b n : ℝ) ^ epsilon) atTop atTop :=
    (tendsto_rpow_atTop epsilon_pos).comp tendsto_b
  exact h.eventually_ge_atTop 2

/-- Eventually `p^ε / 12 ≤ d`. -/
theorem eventually_d_ge : ∀ᶠ n : ℕ in atTop, precision n ^ epsilon / 12 ≤ d n := by
  filter_upwards [eventually_two_le_rpow] with n hn
  unfold d
  have hfloor : (b n : ℝ) ^ epsilon - 1 < ⌊(b n : ℝ) ^ epsilon⌋₊ := Nat.sub_one_lt_floor _
  have hhalf : (b n : ℝ) ^ epsilon / 2 ≤ (b n : ℝ) ^ epsilon - 1 := by linarith
  have hp : precision n ^ epsilon = 6 ^ epsilon * (b n : ℝ) ^ epsilon := by
    rw [precision_eq, Real.mul_rpow (by norm_num) (by positivity)]
  have h6 : (6 : ℝ) ^ epsilon ≤ 6 := by
    calc (6 : ℝ) ^ epsilon ≤ 6 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) epsilon_le_one
      _ = 6 := Real.rpow_one 6
  have hb0 : 0 ≤ (b n : ℝ) ^ epsilon := by positivity
  calc precision n ^ epsilon / 12 = 6 ^ epsilon * (b n : ℝ) ^ epsilon / 12 := by rw [hp]
    _ ≤ 6 * (b n : ℝ) ^ epsilon / 12 := by gcongr
    _ = (b n : ℝ) ^ epsilon / 2 := by ring
    _ ≤ _ := by linarith

end Dimension

section ChunkWidth

/-- The chunk width `K = ⌊d^c⌋` with `c = spacing`. -/
noncomputable def K (n : ℕ) : ℕ := ⌊(d n : ℝ) ^ spacing⌋₊

theorem spacing_pos : 0 < spacing := by norm_num [spacing]
theorem spacing_le_one : spacing ≤ 1 := by norm_num [spacing]

theorem K_le (n : ℕ) : (K n : ℝ) ≤ precision n ^ (epsilon * spacing) := by
  unfold K
  have hd0 : (0 : ℝ) ≤ d n := by positivity
  calc (⌊(d n : ℝ) ^ spacing⌋₊ : ℝ) ≤ (d n : ℝ) ^ spacing := Nat.floor_le (by positivity)
    _ ≤ (precision n ^ epsilon) ^ spacing :=
        Real.rpow_le_rpow hd0 (d_le n) spacing_pos.le
    _ = precision n ^ (epsilon * spacing) := by
        rw [← Real.rpow_mul (precision_pos n).le]

/-- Eventually `p^(εc) / 24 ≤ K`. -/
theorem eventually_K_ge : ∀ᶠ n : ℕ in atTop, precision n ^ (epsilon * spacing) / 24 ≤ K n := by
  have hd : Tendsto (fun n => (d n : ℝ) ^ spacing) atTop atTop := by
    have h1 : Tendsto (fun n => precision n ^ epsilon / 12) atTop atTop :=
      ((tendsto_rpow_atTop epsilon_pos).comp tendsto_precision).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop eventually_d_ge h1
    exact (tendsto_rpow_atTop spacing_pos).comp h2
  filter_upwards [eventually_d_ge, hd.eventually_ge_atTop 2] with n hn h2
  unfold K
  have hfloor : (d n : ℝ) ^ spacing - 1 < ⌊(d n : ℝ) ^ spacing⌋₊ := Nat.sub_one_lt_floor _
  have hp := precision_pos n
  have hp0 : 0 ≤ precision n ^ epsilon / 12 :=
    div_nonneg (Real.rpow_nonneg hp.le _) (by norm_num)
  have hpow : (precision n ^ epsilon / 12) ^ spacing ≤ (d n : ℝ) ^ spacing :=
    Real.rpow_le_rpow hp0 hn spacing_pos.le
  have h12 : (12 : ℝ) ^ spacing ≤ 12 := by
    calc (12 : ℝ) ^ spacing ≤ 12 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) spacing_le_one
      _ = 12 := Real.rpow_one 12
  have hsplit : (precision n ^ epsilon / 12) ^ spacing =
      precision n ^ (epsilon * spacing) / 12 ^ spacing := by
    rw [Real.div_rpow (Real.rpow_nonneg hp.le _) (by norm_num), ← Real.rpow_mul hp.le]
  have hpe : 0 ≤ precision n ^ (epsilon * spacing) := Real.rpow_nonneg hp.le _
  have h12pos : 0 < (12 : ℝ) ^ spacing := Real.rpow_pos_of_pos (by norm_num) _
  have hge : precision n ^ (epsilon * spacing) / 12 ≤ precision n ^ (epsilon * spacing) / 12 ^ spacing :=
    div_le_div_of_nonneg_left hpe h12pos h12
  calc precision n ^ (epsilon * spacing) / 24
      = precision n ^ (epsilon * spacing) / 12 / 2 := by ring
    _ ≤ (d n : ℝ) ^ spacing / 2 := by
        have : precision n ^ (epsilon * spacing) / 12 ≤ (d n : ℝ) ^ spacing := by
          rw [← hsplit] at hge
          exact hge.trans hpow
        linarith
    _ ≤ (d n : ℝ) ^ spacing - 1 := by linarith
    _ ≤ _ := hfloor.le

end ChunkWidth

section Transform

/-- The transform length: the power of two in `[4n/b, 8n/b)`. -/
noncomputable def logT (n : ℕ) : ℕ := ⌈Real.logb 2 (4 * n / b n)⌉₊

noncomputable def T (n : ℕ) : ℝ := 2 ^ logT n

theorem T_pos (n : ℕ) : 0 < T n := by unfold T; positivity

theorem logb_T (n : ℕ) : Real.logb 2 (T n) = logT n := by
  unfold T
  rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]

theorem ratio_pos {n : ℕ} (hn : 1 ≤ n) : 0 < 4 * (n : ℝ) / b n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : (0 : ℝ) < b n := by exact_mod_cast one_le_b n
  positivity

theorem one_le_ratio {n : ℕ} (hn : 1 ≤ n) : 1 ≤ 4 * (n : ℝ) / b n := by
  have hb : (b n : ℝ) ≤ n := by exact_mod_cast b_le_self hn
  have hb0 : (0 : ℝ) < b n := by exact_mod_cast one_le_b n
  rw [le_div_iff₀ hb0]
  linarith

theorem T_lower {n : ℕ} (hn : 1 ≤ n) : 4 * (n : ℝ) / b n ≤ T n := by
  have hx := ratio_pos hn
  have h1 : 4 * (n : ℝ) / b n = 2 ^ Real.logb 2 (4 * n / b n) :=
    (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  rw [h1]
  unfold T logT
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)

theorem T_upper {n : ℕ} (hn : 1 ≤ n) : T n < 8 * (n : ℝ) / b n := by
  have hx := ratio_pos hn
  have h1 : 8 * (n : ℝ) / b n = 2 ^ (Real.logb 2 (4 * n / b n) + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_logb (by norm_num) (by norm_num) hx]
    ring
  rw [h1]
  unfold T logT
  rw [← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  have hy : 0 ≤ Real.logb 2 (4 * n / b n) := Real.logb_nonneg (b := 2) (by norm_num) (one_le_ratio hn)
  exact Nat.ceil_lt_add_one hy

/-- The padded volume `T p` is between `24 n` and `48 n`. -/
theorem volume_bounds {n : ℕ} (hn : 1 ≤ n) :
    24 * (n : ℝ) ≤ T n * precision n ∧ T n * precision n < 48 * n := by
  have hb0 : (0 : ℝ) < b n := by exact_mod_cast one_le_b n
  have hl := T_lower hn
  have hu := T_upper hn
  rw [precision_eq]
  constructor
  · have := mul_le_mul_of_nonneg_right hl (by positivity : (0 : ℝ) ≤ 6 * b n)
    calc 24 * (n : ℝ) = 4 * n / b n * (6 * b n) := by field_simp; ring
      _ ≤ T n * (6 * b n) := this
  · have := mul_lt_mul_of_pos_right hu (by positivity : (0 : ℝ) < 6 * b n)
    calc T n * (6 * (b n : ℝ)) < 8 * n / b n * (6 * b n) := this
      _ = 48 * n := by field_simp; ring

/-- `log₂ n` lies in `(b - 1, b]` for `n ≥ 2`. -/
theorem logb_n_le {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 n ≤ b n := by
  have h := le_two_pow_b n
  have h' : (n : ℝ) ≤ (2 : ℝ) ^ (b n : ℕ) := by exact_mod_cast h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.logb 2 n ≤ Real.logb 2 ((2 : ℝ) ^ (b n : ℕ)) :=
        (Real.logb_le_logb (by norm_num) hn0 (by positivity)).mpr h'
    _ = b n := by rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]

theorem lt_logb_n {n : ℕ} (hn : 2 ≤ n) : (b n : ℝ) - 1 < Real.logb 2 n := by
  have h := two_pow_b_pred_lt hn
  have h' : (2 : ℝ) ^ (b n - 1 : ℕ) < n := by exact_mod_cast h
  have hb := one_le_b n
  have hcast : ((b n - 1 : ℕ) : ℝ) = (b n : ℝ) - 1 := by
    rw [Nat.cast_sub hb]; simp
  calc (b n : ℝ) - 1 = Real.logb 2 ((2 : ℝ) ^ (b n - 1 : ℕ)) := by
        rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num), hcast]
    _ < Real.logb 2 n := Real.logb_lt_logb (by norm_num) (by positivity) h'

/-- Eventually `log₂ b ≤ b / 2`. -/
theorem eventually_logb_b_le : ∀ᶠ n : ℕ in atTop, Real.logb 2 (b n) ≤ (b n : ℝ) / 2 := by
  have hsmall := Real.isLittleO_log_id_atTop.def
    (show (0 : ℝ) < Real.log 2 / 2 by positivity)
  filter_upwards [tendsto_b.eventually hsmall, tendsto_b.eventually_ge_atTop 1] with n hn hb1
  simp only [id, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_nonneg hb1), abs_of_nonneg (by linarith)] at hn
  unfold Real.logb
  rw [div_le_iff₀ (Real.log_pos (by norm_num))]
  linarith

/-- Eventually `b / 2 ≤ log₂ T ≤ b`. -/
theorem eventually_logT_bounds :
    ∀ᶠ n : ℕ in atTop, (b n : ℝ) / 2 ≤ logT n ∧ (logT n : ℝ) ≤ b n := by
  have h8 : ∀ᶠ n : ℕ in atTop, (8 : ℝ) ≤ b n := tendsto_b.eventually_ge_atTop 8
  filter_upwards [eventually_logb_b_le, h8, eventually_ge_atTop 2] with n hlog hb8 hn2
  have hn1 : 1 ≤ n := by omega
  have hx := ratio_pos hn1
  have hb0 : (0 : ℝ) < b n := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hy : Real.logb 2 (4 * n / b n) = 2 + Real.logb 2 n - Real.logb 2 (b n) := by
    rw [Real.logb_div (by positivity) hb0.ne', Real.logb_mul (by norm_num) hn0.ne']
    have : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
    rw [this]
  have hlogn := logb_n_le hn1
  have hlogn' := lt_logb_n hn2
  have hlogb0 : 0 ≤ Real.logb 2 (b n) := Real.logb_nonneg (b := 2) (by norm_num) (by linarith)
  have h3 : (3 : ℝ) ≤ Real.logb 2 (b n) := by
    calc (3 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (3 : ℝ)) := by
          rw [Real.logb_rpow (by norm_num) (by norm_num)]
      _ ≤ Real.logb 2 (b n) := by
          apply (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) hb0).mpr
          rw [show ((2 : ℝ) ^ (3 : ℝ)) = 8 by norm_num]
          exact hb8
  unfold logT
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (b := 2) (by norm_num) (one_le_ratio hn1))
  have hle := Nat.le_ceil (Real.logb 2 (4 * n / b n))
  constructor
  · linarith
  · linarith

end Transform

section AxisLength

/-- The axis exponent `ℓ = ⌈log₂ T / d⌉`. -/
noncomputable def ℓ (n : ℕ) : ℕ := ⌈(logT n : ℝ) / d n⌉₊

/-- Eventually `p / (12 d) ≤ ℓ ≤ p / (3 d)`. -/
theorem eventually_ℓ_bounds :
    ∀ᶠ n : ℕ in atTop,
      precision n / (12 * d n) ≤ ℓ n ∧ (ℓ n : ℝ) ≤ precision n / (3 * d n) := by
  filter_upwards [eventually_logT_bounds] with n ⟨hlo, hhi⟩
  have hd0 : (0 : ℝ) < d n := by exact_mod_cast one_le_d n
  have hdb : (d n : ℝ) ≤ b n := by exact_mod_cast d_le_b n
  have hb0 : (0 : ℝ) < b n := by exact_mod_cast one_le_b n
  unfold ℓ
  rw [precision_eq]
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (logT n : ℝ) / d n)
  have hle := Nat.le_ceil ((logT n : ℝ) / d n)
  constructor
  · calc 6 * (b n : ℝ) / (12 * d n) = (b n : ℝ) / 2 / d n := by field_simp; ring
      _ ≤ (logT n : ℝ) / d n := by gcongr
      _ ≤ _ := hle
  · have h1 : (logT n : ℝ) / d n ≤ (b n : ℝ) / d n := by gcongr
    have h2 : (1 : ℝ) ≤ (b n : ℝ) / d n := by rw [le_div_iff₀ hd0]; linarith
    refine le_of_lt ?_
    calc (⌈(logT n : ℝ) / d n⌉₊ : ℝ) < (logT n : ℝ) / d n + 1 := hceil
      _ ≤ (b n : ℝ) / d n + (b n : ℝ) / d n := by linarith
      _ = 6 * (b n : ℝ) / (3 * d n) := by field_simp; ring

/-- The axis length `r = 2^ℓ` is at least `2^(p / (12 d))`, and `d ≤ p^ε`. -/
noncomputable def r (n : ℕ) : ℝ := 2 ^ ℓ n

/-- Eventually `r ≥ 2^(p^(1-ε) / 12)`, so `r` exceeds every fixed power of `p`. -/
theorem eventually_r_ge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (precision n ^ (1 - epsilon) / 12) ≤ r n := by
  filter_upwards [eventually_ℓ_bounds] with n ⟨hlo, _⟩
  unfold r
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  refine le_trans ?_ hlo
  have hd := d_le n
  have hd0 : (0 : ℝ) < d n := by exact_mod_cast one_le_d n
  have hp := precision_pos n
  have hpe : 0 < precision n ^ epsilon := by positivity
  calc precision n ^ (1 - epsilon) / 12 = precision n / precision n ^ epsilon / 12 := by
        rw [Real.rpow_sub hp, Real.rpow_one]
    _ ≤ precision n / d n / 12 := by gcongr
    _ = precision n / (12 * d n) := by field_simp

end AxisLength

end IntegerMultBounds.Sizes
