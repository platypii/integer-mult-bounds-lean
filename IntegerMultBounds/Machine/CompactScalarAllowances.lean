import IntegerMultBounds.Sizes
import IntegerMultBounds.Asymptotics

/-! The actual multiplier choices d=floor(b^epsilon), K=floor(d^spacing)
and p=6b pay the complete original-axis repair size. No independent cubic
address-width hypothesis is needed once D is an original subset of d axes. -/
namespace IntegerMultBounds.Machine.CompactScalarAllowances
noncomputable section
open Sizes TimeBound Parameters

 theorem chunk_le_dimension (n : ℕ) : K n≤d n := by
  have hd : (1:ℝ)≤d n := by exact_mod_cast one_le_d n
  have hpow : (d n:ℝ)^spacing≤d n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hd spacing_le_one
  unfold K
  exact_mod_cast (Nat.floor_le (by positivity : (0:ℝ)≤(d n:ℝ)^spacing)).trans hpow

 theorem original_axis_size (n D : ℕ) (hD : D≤d n) :
    ((D*K n+3:ℕ):ℝ)≤precision n^2 := by
  have hprod : D*K n≤b n*b n :=
    Nat.mul_le_mul (hD.trans (d_le_b n)) ((chunk_le_dimension n).trans (d_le_b n))
  have hh : (D:ℝ)*(K n:ℝ)≤(b n:ℝ)*(b n:ℝ) := by exact_mod_cast hprod
  have hb : (1:ℝ)≤b n := by exact_mod_cast one_le_b n
  rw [Nat.cast_add,Nat.cast_mul,precision_eq]
  norm_num only [Nat.cast_ofNat]
  nlinarith [sq_nonneg ((b n:ℝ)-1)]

 theorem original_axis_cubic (n D : ℕ) (hD : D≤d n) :
    ((D*K n+3:ℕ):ℝ)≤precision n^3 := by
  have hp : (1:ℝ)≤precision n := by linarith [six_le_precision n]
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg (precision n))
  rw [mul_one,←pow_succ] at hh
  exact (original_axis_size n D hD).trans hh

 theorem selected_count (n f : ℕ) (hf : f≤d n) : ((f-1:ℕ):ℝ)≤precision n := by
  have hh : f-1≤b n := (Nat.sub_le f 1).trans (hf.trans (d_le_b n))
  have hr : ((f-1:ℕ):ℝ)≤b n := by exact_mod_cast hh
  rw [precision_eq]
  linarith [Nat.cast_nonneg (α:=ℝ) (b n)]

open Filter

/-- The actual polynomial axis length eventually dominates the precision. -/
 theorem eventually_axis_ge_precision : ∀ᶠ n : ℕ in atTop, precision n≤r n := by
  have hexponent : 0<1-epsilon := by norm_num [epsilon]
  have hsmall := (isLittleO_log_rpow_atTop hexponent).def
    (show (0:ℝ)<Real.log 2/12 by positivity)
  filter_upwards [tendsto_precision.eventually hsmall,eventually_r_ge] with n hn hr
  have hp : 1≤precision n := by linarith [six_le_precision n]
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_nonneg hp),
    abs_of_nonneg (Real.rpow_nonneg (precision_pos n).le _)] at hn
  have he : precision n≤(2:ℝ)^(precision n^(1-epsilon)/12) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    calc
      precision n = Real.exp (Real.log (precision n)) := (Real.exp_log (precision_pos n)).symm
      _ ≤ Real.exp (Real.log 2*(precision n^(1-epsilon)/12)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hn]
  exact he.trans hr

def guardLog (n : ℕ) := Nat.clog 2 (6*b n)

theorem precision_dyadic (n : ℕ) : precision n≤(2:ℝ)^guardLog n := by
  have h := Nat.le_pow_clog (by decide : 1<2) (6*b n)
  have hh : ((6*b n:ℕ):ℝ)≤(2:ℝ)^guardLog n := by exact_mod_cast h
  simpa only [Nat.cast_mul,Nat.cast_ofNat,precision_eq] using hh

/-- The actual floor chunk width eventually meets the logarithmic guard
allowance; no independent sufficiently-large-chunk premise is supplied. -/
 theorem eventually_guard_fits : ∀ᶠ n : ℕ in atTop, 8*guardLog n+16≤K n := by
  have ha : 0<epsilon*spacing := mul_pos epsilon_pos spacing_pos
  have hsmall := (isLittleO_log_rpow_atTop ha).def
    (show (0:ℝ)<Real.log 2/384 by positivity)
  have hg := ((tendsto_rpow_atTop ha).comp tendsto_precision).eventually_ge_atTop 1152
  filter_upwards [tendsto_precision.eventually hsmall,hg,eventually_K_ge] with n hn hg hk
  change 1152≤precision n^(epsilon*spacing) at hg
  have hp : 1≤precision n := by linarith [six_le_precision n]
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Real.log_nonneg hp),
    abs_of_nonneg (Real.rpow_nonneg (precision_pos n).le _)] at hn
  have hlog : Real.logb 2 (precision n)≤precision n^(epsilon*spacing)/384 := by
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    nlinarith only [hn]
  have hceil : (guardLog n:ℝ)<Real.logb 2 (precision n)+1 := by
    have hh := Nat.ceil_lt_add_one
      (Real.logb_nonneg (b:=2) (by norm_num) hp)
    have he : precision n=((6*b n:ℕ):ℝ) := by simp only [precision_eq,Nat.cast_mul,Nat.cast_ofNat]
    have hc : ⌈Real.logb 2 ((6*b n:ℕ):ℝ)⌉₊=Nat.clog 2 (6*b n) := by
      simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (6*b n)
    rw [he,hc] at hh
    simpa only [guardLog,he] using hh
  have hh : ((8*guardLog n+16:ℕ):ℝ)≤K n := by
    push_cast
    nlinarith only [hceil,hlog,hg,hk]
  exact_mod_cast hh

/-- Original polynomial record bits pay the complete padded repair address.
Only the literal record-width comparison remains, rather than a free repair
width assumption for each node. -/
 theorem eventually_record_allowance : ∀ᶠ n : ℕ in atTop,
    ∀ D payload : ℕ, D≤d n → 6*b n*2^ℓ n≤payload → D*K n+3≤payload := by
  filter_upwards [eventually_axis_ge_precision] with n hr D payload hD hpayload
  have hs := original_axis_size n D hD
  have hp : 0≤precision n := (precision_pos n).le
  have hmul := mul_le_mul_of_nonneg_left hr hp
  have hpay : precision n*r n≤(payload:ℝ) := by
    have hh : ((6*b n*2^ℓ n:ℕ):ℝ)≤payload := by exact_mod_cast hpayload
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,precision_eq,r] using hh
  have hh : ((D*K n+3:ℕ):ℝ)≤payload := by
    calc
      _ ≤ precision n^2 := hs
      _ = precision n*precision n := by ring
      _ ≤ precision n*r n := hmul
      _ ≤ _ := hpay
  exact_mod_cast hh

end
end IntegerMultBounds.Machine.CompactScalarAllowances
