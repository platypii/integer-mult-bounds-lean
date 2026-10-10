import IntegerMultBounds.Machine.CompactNativeRolePaddingBudget
import IntegerMultBounds.Machine.CompactReservationNativePaddingActualBudget

/-! Actual multiplier scalars pay the complete native reservation-role caller
with the certified saving, using the fixed machine's genuine Hoare runtime. -/
namespace IntegerMultBounds.Machine.CompactNativeRolePaddingActualBudget
noncomputable section
open Filter Sizes Parameters
open CompactReservationGrowth (guard reserved)
open CompactFallbackScalars (precision)
open CompactFallbackActualBudget (baseVolume volume_le_base)
open CompactFallbackAxisRun (Array Width)
open ActivePrefixStageParameters (Stage)
open CompactNativeRoleControllerBudget (controller)
open Networks

abbrev stage (c m n D : ℕ) :=
  Stage (CompactReservationNativeRows.shape c m (d n) D (guard n) (K n))
def cost (inverse : Bool) (c m n D : ℕ) (v : stage c m n D) (f : Array D (K n) (ℓ n)) :=
  CompactNativeRolePaddingCaller.cost inverse c m D (K n) v.rho (ℓ n) (precision n) (d n) (guard n) f (controller v)
def constant (c m : ℕ) := 5*CompactNativeRolePaddingBudget.constant c m

theorem eventually_depth_positive (m : ℕ) (hm : 2≤m) :
    ∀ᶠ n : ℕ in atTop, 0<CompactGlobalRowPadding.depth m (d n) := by
  have ht : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop eventually_d_ge
      (((tendsto_rpow_atTop epsilon_pos).comp TimeBound.tendsto_precision).atTop_div_const (by norm_num))
  filter_upwards [ht.eventually_ge_atTop 2] with n hn
  have hd : 1<d n := by exact_mod_cast (show (1:ℝ)<d n by linarith)
  exact Nat.clog_pos (by omega) hd

theorem cost_le (inverse : Bool) (c m n D : ℕ) (v : stage c m n D) (hc : 2≤c) (hm : 2≤m)
    (hD : D≤d n) (hres : reserved c m n≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m (d n)) (f : Array D (K n) (ℓ n))
    (hw : Width D (K n) (ℓ n) (precision n) f) :
    cost inverse c m n D v f≤constant c m*baseVolume n D*reserved c m n := by
  have hh := CompactNativeRolePaddingBudget.cost_linear inverse c m D (K n) (ℓ n) (precision n) (d n) (guard n)
    v hc hm (one_le_d n) (by unfold CompactReservationGrowth.guard; omega)
    (CompactReservationCutoff.positive_chunk n) hres hdepth f hw
  have hv := Nat.mul_le_mul_right (reserved c m n)
    (Nat.mul_le_mul_left (CompactNativeRolePaddingBudget.constant c m) (volume_le_base n D hD))
  simpa only [cost,constant,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh.trans hv

private theorem eventually_scale (c m C : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ V : ℕ,
      (C*V*reserved c m n:ℝ)≤η*(V:ℝ)*(d n:ℝ)^lam' := by
  have hs : (0:ℝ)<C+1 := by positivity
  filter_upwards [CompactReservationRate.eventually_reserved_power c m hm lam' (η/(C+1))
    CompactReservationRate.certified_exponent (div_pos hη hs)] with n hn V
  have he := (le_div_iff₀ hs).mp (show (reserved c m n:ℝ)≤(η*(d n:ℝ)^lam')/(C+1) by
    convert hn using 1; ring)
  have hscale := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) V)
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) (d n)) lam']

theorem eventually_cost (inverse : Bool) (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, D≤d n → reserved c m n≤D →
      ∀ v : stage c m n D, ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      (cost inverse c m n D v f:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_scale c m (constant c m) hm η hη, eventually_depth_positive m hm] with n hn hdepth D hD hres v f hw
  have hh : (cost inverse c m n D v f:ℝ)≤(constant c m:ℝ)*(baseVolume n D:ℝ)*(reserved c m n:ℝ) := by
    exact_mod_cast cost_le inverse c m n D v hc hm hD hres hdepth f hw
  exact hh.trans (hn _)

/-- Fixed paid native preparation machine; the runtime is its actual cost. -/
theorem eventually_execution (inverse : Bool) (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, D≤d n → ∀ hres : reserved c m n≤D,
      ∀ hdepth : 0<CompactGlobalRowPadding.depth m (d n),
      ∀ v : stage c m n D, v.rho<K n →
      ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      ∃ t : ℕ, HoareTime (CompactNativeRolePaddingCaller.program inverse c m)
        (fun w => w=CleanSubbank.bank (s:=CompactNativeRoleSourcePorts.localTapes c)
          (((CompactNativeRoleReservedCaller.original
            (CompactReservedHeaders.initial D (K n) v.rho (ℓ n) (precision n) (d n) (guard n))
            (CompactNativeRolePaddingCaller.payload c (NativeZeroPaddingArray.word f))
            (SharedBank.empty CompactNativeRolePaddingCaller.remainder 2) (controller v)).append
            (SharedBank.empty 43 2)).append (SharedBank.empty c 2)))
        (fun w => w=CompactNativeRoleReservedCaller.output inverse c m D (K n) v.rho (ℓ n)
          (precision n) (d n) (guard n) (by omega) (CompactReservationCutoff.positive_chunk n)
          hres hdepth f (SharedBank.empty CompactNativeRolePaddingCaller.remainder 2) (controller v)) t ∧
        (t:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_cost inverse c m hc hm η hη] with n hn D hD hres hdepth v hr f hw
  have hDp := (CompactReservedVolumeBudget.geometry c m D (K n) (d n) (guard n)
    (one_le_d n) (by unfold CompactReservationGrowth.guard; omega)
    (CompactReservationCutoff.positive_chunk n) hres).2.1
  exact ⟨cost inverse c m n D v f,
    CompactNativeRolePaddingCaller.splits inverse c m D (K n) v.rho (ℓ n) (precision n) (d n) (guard n)
      hc hm (one_le_d n) (by unfold CompactReservationGrowth.guard; omega)
      (CompactReservationCutoff.positive_chunk n) hr hDp hres hdepth f hw (controller v),
    hn D hD hres v f hw⟩

end
end IntegerMultBounds.Machine.CompactNativeRolePaddingActualBudget
