import IntegerMultBounds.Machine.CompactReservationCutoff

/-! Quantitative reservation savings for the actual small-dimension fallback.
The actual cutoff is negligible relative to d^a for every a>1-spacing, in
particular the certified lam' exponent. Merely being o(d) would not suffice. -/
namespace IntegerMultBounds.Machine.CompactReservationRate
noncomputable section
open Filter Asymptotics Sizes TimeBound Parameters CompactScalarAllowances
open CompactReservationGrowth CompactReservationCutoff

theorem dimension_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop eventually_d_ge
    (((tendsto_rpow_atTop epsilon_pos).comp tendsto_precision).atTop_div_const (by norm_num))

theorem eventually_guard_power (a η : ℝ) (ha : 0<a) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, (guardLog n : ℝ)+1≤η*(d n : ℝ)^a := by
  have hex : 0<epsilon*a := mul_pos epsilon_pos ha
  have hden : (0:ℝ)<(12:ℝ)^a := by positivity
  have hsmall := (isLittleO_log_rpow_atTop hex).def
    (show (0:ℝ)<η*Real.log 2/(2*(12:ℝ)^a) by positivity)
  have hlarge := ((tendsto_rpow_atTop hex).comp tendsto_precision).eventually_ge_atTop
    (4*(12:ℝ)^a/η)
  filter_upwards [tendsto_precision.eventually hsmall,hlarge,eventually_d_ge] with n hn hl hd
  have hp : 1≤precision n := by linarith [six_le_precision n]
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_nonneg hp),abs_of_nonneg (Real.rpow_nonneg (precision_pos n).le _)] at hn
  have hlog : Real.logb 2 (precision n)≤η/(2*(12:ℝ)^a)*precision n^(epsilon*a) := by
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    convert hn using 1; ring
  have hc : 2≤η/(2*(12:ℝ)^a)*precision n^(epsilon*a) := by
    change 4*(12:ℝ)^a/η≤precision n^(epsilon*a) at hl
    have hh := (div_le_iff₀ hη).mp hl
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos (by norm_num) hden)).mpr
    nlinarith only [hh]
  have hpow : precision n^(epsilon*a)/(12:ℝ)^a≤(d n:ℝ)^a := by
    rw [Real.rpow_mul (precision_pos n).le,←Real.div_rpow (by positivity) (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) hd ha.le
  have hceil := CompactGuardGrowth.guardLog_lt_log n
  calc
    (guardLog n:ℝ)+1≤2*(η/(2*(12:ℝ)^a)*precision n^(epsilon*a)) := by linarith only [hceil,hlog,hc]
    _=η/(12:ℝ)^a*precision n^(epsilon*a) := by ring
    _=η*(precision n^(epsilon*a)/(12:ℝ)^a) := by ring
    _≤η*(d n:ℝ)^a := mul_le_mul_of_nonneg_left hpow hη.le

theorem eventually_chunk_half :
    ∀ᶠ n : ℕ in atTop, (d n:ℝ)^spacing/2≤(K n:ℝ) := by
  have h := ((tendsto_rpow_atTop spacing_pos).comp dimension_tendsto).eventually_ge_atTop 2
  filter_upwards [h] with n hn
  change 2≤(d n:ℝ)^spacing at hn
  have hf : (d n:ℝ)^spacing-1<(K n:ℝ) := Nat.sub_one_lt_floor _
  linarith

theorem eventually_rate_bound (c m : ℕ) (hm : 2≤m) :
    ∀ᶠ n : ℕ in atTop, (reserved c m n:ℝ)≤
      2*((Nat.clog 2 c:ℝ)+20)*((guardLog n:ℝ)+1)*(d n:ℝ)^(1-spacing) := by
  filter_upwards [eventually_chunk_half] with n hk
  have hd : (0:ℝ)<d n := by exact_mod_cast one_le_d n
  have hpow : (0:ℝ)<(d n:ℝ)^spacing := by positivity
  let η : ℝ := 2*((guardLog n:ℝ)+1)/(d n:ℝ)^spacing
  have hη : 0<η := by dsimp [η]; positivity
  have hs : (guardLog n:ℝ)+1≤η*(K n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hk hη.le
    have he : η*((d n:ℝ)^spacing/2)=(guardLog n:ℝ)+1 := by dsimp [η]; field_simp
    rwa [he] at hh
  have hr := reservation_bound c m n hm η hη hs
  have he : ((Nat.clog 2 c:ℝ)+20)*η*(d n:ℝ)=
      2*((Nat.clog 2 c:ℝ)+20)*((guardLog n:ℝ)+1)*(d n:ℝ)^(1-spacing) := by
    rw [Real.rpow_sub hd,Real.rpow_one]
    dsimp [η]
    ring
  rwa [he] at hr

/-- Any exponent strictly above the actual reservation exponent pays all
individually processed axes, uniformly in the selected dimension. -/
theorem eventually_reserved_power (c m : ℕ) (hm : 2≤m) (a η : ℝ)
    (ha : 1-spacing<a) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, (reserved c m n:ℝ)≤η*(d n:ℝ)^a := by
  have hC : (0:ℝ)<2*((Nat.clog 2 c:ℝ)+20) := by positivity
  filter_upwards [eventually_rate_bound c m hm,
    eventually_guard_power (a-(1-spacing)) (η/(2*((Nat.clog 2 c:ℝ)+20)))
      (by linarith) (div_pos hη hC)] with n hr hg
  have hd : (0:ℝ)<d n := by exact_mod_cast one_le_d n
  have he : (d n:ℝ)^(a-(1-spacing))*(d n:ℝ)^(1-spacing)=(d n:ℝ)^a := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  calc
    (reserved c m n:ℝ)≤2*((Nat.clog 2 c:ℝ)+20)*((guardLog n:ℝ)+1)*(d n:ℝ)^(1-spacing) := hr
    _≤2*((Nat.clog 2 c:ℝ)+20)*(η/(2*((Nat.clog 2 c:ℝ)+20))*(d n:ℝ)^(a-(1-spacing)))*(d n:ℝ)^(1-spacing) := by gcongr
    _=η*((d n:ℝ)^(a-(1-spacing))*(d n:ℝ)^(1-spacing)) := by field_simp
    _=η*(d n:ℝ)^a := by rw [he]

theorem eventually_cutoff_power (c m : ℕ) (hm : 2≤m) (a η : ℝ)
    (ha : 1-spacing<a) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, (cutoff c m n:ℝ)≤η*(d n:ℝ)^a := by
  filter_upwards [eventually_reserved_power c m hm a (η/2) ha (by positivity)] with n hn
  unfold cutoff
  push_cast
  linarith

theorem cutoff_littleO_power (c m : ℕ) (hm : 2≤m) (a : ℝ) (ha : 1-spacing<a) :
    (fun n : ℕ => (cutoff c m n:ℝ)) =o[atTop] (fun n => (d n:ℝ)^a) := by
  apply IsLittleO.of_bound
  intro η hη
  filter_upwards [eventually_cutoff_power c m hm a η ha hη] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) _) _)] using hn

theorem certified_exponent : 1-spacing<lam' := by norm_num [spacing,lam']

theorem cutoff_littleO_certified (c m : ℕ) (hm : 2≤m) :
    (fun n : ℕ => (cutoff c m n:ℝ)) =o[atTop] (fun n => (d n:ℝ)^lam') :=
  cutoff_littleO_power c m hm lam' certified_exponent

/-- A linear per-axis kernel pays all individually processed axes at the
certified exponent, uniformly in every selected dimension. Kernel execution
and its volume bound must still be supplied by the physical fallback proof. -/
theorem eventually_processed_certified (c m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (processed c m n D:ℝ)≤η*(d n:ℝ)^lam' := by
  filter_upwards [eventually_reserved_power c m hm lam' η certified_exponent hη] with n hn D
  have h : (processed c m n D:ℝ)≤(reserved c m n:ℝ) := by
    exact_mod_cast min_le_right D (reserved c m n)
  exact h.trans hn

end
end IntegerMultBounds.Machine.CompactReservationRate
