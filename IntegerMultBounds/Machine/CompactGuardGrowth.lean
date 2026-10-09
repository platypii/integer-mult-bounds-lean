import IntegerMultBounds.Machine.CompactScalarAllowances

/-! The actual ceiling logarithmic guard is negligible relative to the
actual floor chunk width. This quantifies the eventual guard allowance with
any positive coefficient, rather than only one fixed safety margin. -/
namespace IntegerMultBounds.Machine.CompactGuardGrowth
noncomputable section
open Filter Asymptotics Sizes TimeBound Parameters CompactScalarAllowances

theorem guardLog_lt_log (n : ℕ) :
    (guardLog n:ℝ)<Real.logb 2 (precision n)+1 := by
  have hp : 1≤precision n := by linarith [six_le_precision n]
  have hh := Nat.ceil_lt_add_one (Real.logb_nonneg (b:=2) (by norm_num) hp)
  have he : precision n=((6*b n:ℕ):ℝ) := by simp only [precision_eq,Nat.cast_mul,Nat.cast_ofNat]
  have hc : ⌈Real.logb 2 ((6*b n:ℕ):ℝ)⌉₊=Nat.clog 2 (6*b n) := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (6*b n)
  rw [he,hc] at hh
  simpa only [guardLog,he] using hh

theorem eventually_guard_small (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, (guardLog n:ℝ)+1≤η*(K n:ℝ) := by
  have ha : 0<epsilon*spacing := mul_pos epsilon_pos spacing_pos
  have hsmall := (isLittleO_log_rpow_atTop ha).def
    (show (0:ℝ)<η*Real.log 2/48 by positivity)
  have hg := ((tendsto_rpow_atTop ha).comp tendsto_precision).eventually_ge_atTop (96/η)
  filter_upwards [tendsto_precision.eventually hsmall,hg,eventually_K_ge] with n hn hg hk
  change 96/η≤precision n^(epsilon*spacing) at hg
  have hp : 1≤precision n := by linarith [six_le_precision n]
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_nonneg hp),
    abs_of_nonneg (Real.rpow_nonneg (precision_pos n).le _)] at hn
  have hlog : Real.logb 2 (precision n)≤η*precision n^(epsilon*spacing)/48 := by
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    nlinarith only [hn]
  have hlarge : 96≤η*precision n^(epsilon*spacing) := by
    have h := (div_le_iff₀ hη).mp hg
    nlinarith only [h]
  have hceil := guardLog_lt_log n
  have hk' := mul_le_mul_of_nonneg_left hk hη.le
  nlinarith only [hlog,hlarge,hceil,hk']

theorem guard_littleO_chunk :
    (fun n : ℕ => (guardLog n:ℝ)+1) =o[atTop] (fun n => (K n:ℝ)) := by
  apply IsLittleO.of_bound
  intro η hη
  filter_upwards [eventually_guard_small η hη] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤(guardLog n:ℝ)+1),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (K n))] using hn

end
end IntegerMultBounds.Machine.CompactGuardGrowth
