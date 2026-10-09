import IntegerMultBounds.Machine.CompactFallbackRoundtrip
import IntegerMultBounds.Machine.CompactFallbackActualBudget

/-! The complete physical sparse roundtrip, including both ordinal lifecycles,
has the actual small-dimension cutoff saving at the original coefficient count. -/
namespace IntegerMultBounds.Machine.CompactFallbackRoundtripBudget
noncomputable section
open Filter Sizes Parameters
open CompactFallbackScalars (precision)
open CompactFallbackActualBudget (baseVolume volume_le_base)

theorem eventually_cost (c m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, D≤d n → D≤CompactReservationGrowth.reserved c m n →
      (CompactFallbackRoundtrip.constant*CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n)*D : ℝ)≤
        η*(baseVolume n D : ℝ)*(d n : ℝ)^lam' := by
  have hs : (0:ℝ)<5*CompactFallbackRoundtrip.constant+1 := by positivity
  filter_upwards [CompactReservationRate.eventually_processed_certified c m hm
    (η/(5*CompactFallbackRoundtrip.constant+1)) (div_pos hη hs)] with n hn D hD hsmall
  have hc := hn D
  rw [(CompactReservationCutoff.fallback c m n D hsmall).1] at hc
  have hv : (CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n):ℝ)≤5*(baseVolume n D:ℝ) := by
    exact_mod_cast volume_le_base n D hD
  have hc' : (D:ℝ)≤(η*(d n:ℝ)^lam')/(5*CompactFallbackRoundtrip.constant+1) := by
    convert hc using 1; ring
  have he := (le_div_iff₀ hs).mp hc'
  calc
    _≤(CompactFallbackRoundtrip.constant:ℝ)*(5*(baseVolume n D:ℝ))*(D:ℝ) := by gcongr
    _≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
      have hscale := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) (baseVolume n D))
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) (d n)) lam']


end
end IntegerMultBounds.Machine.CompactFallbackRoundtripBudget
