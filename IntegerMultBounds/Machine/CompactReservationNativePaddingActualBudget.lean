import IntegerMultBounds.Machine.CompactReservationNativePaddingBudget
import IntegerMultBounds.Machine.CompactReservedActualBudget

/-! The actual scalar endpoint pays original reservation, adapter headers,
genuine native zero padding and all cleanup, with the certified saving. -/
namespace IntegerMultBounds.Machine.CompactReservationNativePaddingActualBudget
noncomputable section
open Filter Sizes Parameters
open CompactReservationGrowth (guard reserved)
open CompactFallbackScalars (precision)
open CompactFallbackActualBudget (baseVolume volume_le_base)
open CompactFallbackAxisRun (Array Width word)
open CompactFallbackSemantics (decoded)
open Networks

def cost (inverse : Bool) (c m n D rho : ℕ) (f : Array D (K n) (ℓ n)) :=
  CompactReservationNativePadding.cost inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n) f
def constant (c m : ℕ) := 5*CompactReservationNativePaddingBudget.constant c m

theorem cost_le (inverse : Bool) (c m n D rho : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hD : D≤d n) (hres : reserved c m n≤D) (f : Array D (K n) (ℓ n))
    (hw : Width D (K n) (ℓ n) (precision n) f) :
    cost inverse c m n D rho f≤constant c m*baseVolume n D*reserved c m n := by
  have hh := CompactReservationNativePaddingBudget.cost_linear inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc hm (one_le_d n) (by unfold CompactReservationGrowth.guard; omega) (CompactReservationCutoff.positive_chunk n) hres f hw
  have hv := Nat.mul_le_mul_right (reserved c m n)
    (Nat.mul_le_mul_left (CompactReservationNativePaddingBudget.constant c m) (volume_le_base n D hD))
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
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D →
      ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      (cost inverse c m n D rho f:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_scale c m (constant c m) hm η hη] with n hn D rho hD hres f hw
  have hh : (cost inverse c m n D rho f:ℝ)≤(constant c m:ℝ)*(baseVolume n D:ℝ)*(reserved c m n:ℝ) := by
    exact_mod_cast cost_le inverse c m n D rho hc hm hD hres f hw
  exact hh.trans (hn _)

/-- A concrete fixed one-pass machine and its actual fully paid cost witness. -/
theorem eventually_execution (inverse : Bool) (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D → rho<K n →
      ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      ∃ t : ℕ, HoareTime (CompactReservationNativePadding.program inverse c m)
        (fun v => v=CompactReservationNativePadding.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n)) (NativeZeroPaddingArray.word f))
        (fun v => v=CompactReservationNativePadding.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n))
          (CompactReservationNativePadding.result inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n) f)) t ∧
        (t:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_cost inverse c m hc hm η hη] with n hn D rho hD hres hr f hw
  exact ⟨cost inverse c m n D rho f,CompactReservationNativePadding.runs inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc hm (one_le_d n) (CompactReservationCutoff.positive_chunk n) hr (by
      have hh := CompactReservedVolumeBudget.geometry c m D (K n) (d n) (guard n)
        (one_le_d n) (by unfold CompactReservationGrowth.guard; omega) (CompactReservationCutoff.positive_chunk n) hres
      exact hh.2.1) hres f hw,hn D rho hD hres f hw⟩

end
end IntegerMultBounds.Machine.CompactReservationNativePaddingActualBudget
