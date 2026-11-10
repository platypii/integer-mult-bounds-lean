module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLogGrowth

/-! The retained-halo traversal pays a local logarithm, once per axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

/-- Linear precision times a local logarithm fits the numerical exponent. -/
theorem precision_mul_log_le (p : ℕ) (hp : 1 ≤ p) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (p : ℝ)*(a*((Nat.log 2 p+1 : ℕ) : ℝ)+b) ≤
      (512*a+b)*(p : ℝ)^(129/128 : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hlog := (compact_natLog_succ_le hp).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hp1 (show (1/256 : ℝ) ≤ 1/128 by norm_num))
      (by norm_num : (0 : ℝ) ≤ 512))
  have hone := Real.one_le_rpow hp1 (by norm_num : (0 : ℝ) ≤ 1/128)
  have hlocal : a*((Nat.log 2 p+1 : ℕ) : ℝ)+b ≤
      (512*a+b)*(p : ℝ)^(1/128 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog ha
    have hh' := mul_le_mul_of_nonneg_left hone hb
    nlinarith only [hh,hh']
  calc
    _ ≤ (p : ℝ)*((512*a+b)*(p : ℝ)^(1/128 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlocal hp0.le
    _ = _ := by
      rw [show (129/128 : ℝ) = 1+1/128 by norm_num,
        Real.rpow_add hp0,Real.rpow_one]
      ring

/-- The exact all-axis routing bill, with startup retained separately. -/
theorem manuscriptHaloTime_le (p w volume d startup cW : ℕ)
    (hp : 1 ≤ p) (hw : w ≤ cW*p) :
    ((startup+d*((volume*w)*(8928*(Nat.log 2 p+1)+6654)+3)+2 : ℕ) : ℝ) ≤
      (startup : ℝ)+(d : ℝ)*
        (4577790*(cW : ℝ)*volume*(p : ℝ)^(129/128 : ℝ)+3)+2 := by
  have hlog := precision_mul_log_le p hp 8928 6654 (by norm_num) (by norm_num)
  have hw' : (w : ℝ) ≤ (cW : ℝ)*p := by exact_mod_cast hw
  have hlocal : (w : ℝ)*(8928*((Nat.log 2 p+1 : ℕ) : ℝ)+6654) ≤
      4577790*(cW : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ ((cW : ℝ)*p)*(8928*((Nat.log 2 p+1 : ℕ) : ℝ)+6654) :=
        mul_le_mul_of_nonneg_right hw' (by positivity)
      _ = (cW : ℝ)*((p : ℝ)*(8928*((Nat.log 2 p+1 : ℕ) : ℝ)+6654)) := by ring
      _ ≤ (cW : ℝ)*((512*8928+6654)*(p : ℝ)^(129/128 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = _ := by ring
  have hvolume := mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg volume)
  have hd := mul_le_mul_of_nonneg_left hvolume (Nat.cast_nonneg d)
  push_cast at hd ⊢
  nlinarith only [hd]

end IntegerMultBounds.MathlibTM2.Cost
