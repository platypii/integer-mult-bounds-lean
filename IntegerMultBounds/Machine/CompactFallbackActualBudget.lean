import IntegerMultBounds.Machine.CompactFallbackOriginal

/-! Actual multiplier choices instantiate the physical sparse-axis fallback.
Its coefficient count and original signed-width reservation determine the real
native volume; the paid per-axis costs, not an abstract work oracle, now fill
CompactFallbackBudget uniformly at the actual cutoff. -/
namespace IntegerMultBounds.Machine.CompactFallbackActualBudget
noncomputable section
open Filter Sizes Parameters
open CompactFallbackScalars (precision nativePayload coefficientCount)

def baseVolume (n D : ℕ) := 2^(D*K n)*(6*b n*2^ℓ n)
def axisCost (n D rho i : ℕ) := CompactFallbackAxisRun.cost D (K n) rho (ℓ n) (precision n) i

theorem actual_volume (n D : ℕ) :
    CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n)=2^(D*K n)*nativePayload n D := by
  unfold CompactFallbackAxisRun.volume ButterflyAxisHeadersBudget.logicalVolume
    ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width
    CompactFallbackHeaders.bits CompactFallbackHeaders.polynomials CompactFallbackHeaders.reservation
    nativePayload CompactFallbackScalars.width CompactFallbackScalars.binaryDimension
    CompactFallbackScalars.polynomialCount
  unfold CompactFallbackHeaders.bits
  ring

theorem volume_le_base (n D : ℕ) (hD : D≤d n) :
    CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n)≤5*baseVolume n D := by
  rw [actual_volume]
  have hh := Nat.mul_le_mul_left (2^(D*K n)) (CompactFallbackScalars.payload_bounds n D hD).2
  unfold baseVolume CompactFallbackScalars.polynomialCount at *
  nlinarith

theorem actual_width (n D : ℕ) (f : CompactFallbackAxisRun.Array D (K n) (ℓ n)) :
    CompactFallbackAxisRun.Width D (K n) (ℓ n) (precision n) f ↔
      ∀ i,(f i).1.length=CompactFallbackScalars.width n D ∧ (f i).2.length=CompactFallbackScalars.width n D := by
  have he : ButterflyGuard.width (CompactFallbackHeaders.reservation D (K n) (precision n))
      (CompactFallbackHeaders.bits D (K n))=CompactFallbackScalars.width n D := by
    unfold ButterflyGuard.width ButterflyGuard.halfWidth CompactFallbackHeaders.reservation
      CompactFallbackHeaders.bits CompactFallbackScalars.width CompactFallbackScalars.binaryDimension
    omega
  unfold CompactFallbackAxisRun.Width ButterflyAxisArray.Width
  rw [he]

theorem actual_count (n D : ℕ) :
    ButterflyAxisArray.Size (CompactFallbackHeaders.bits D (K n)) (CompactFallbackHeaders.polynomials (ℓ n))=
      coefficientCount n D := rfl

def constant := 5*CompactFallbackAxisBudget.constant

theorem axisCost_le (n D rho i : ℕ) (hD : D≤d n) (hr : rho<K n) (hi : i<D) :
    axisCost n D rho i≤constant*baseVolume n D := by
  have h0 := CompactFallbackAxisBudget.cost_linear D (K n) rho (ℓ n) (precision n) i
    (CompactReservationCutoff.positive_chunk n) hr hi
  have h1 := Nat.mul_le_mul_left CompactFallbackAxisBudget.constant (volume_le_base n D hD)
  unfold axisCost constant
  nlinarith

/-- Every row in the aggregate is the proved cost of the fixed original-input
sparse-axis machine, including its derived-header work and complete cleanup. -/
theorem eventually_cost (c m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → rho<K n →
      (CompactFallbackBudget.cost c m n D (axisCost n D rho) : ℝ)≤
        η*(baseVolume n D : ℝ)*(d n : ℝ)^lam' := by
  filter_upwards [CompactFallbackBudget.eventually_cost c m constant hm η hη] with n hn D rho hD hr
  exact hn D (baseVolume n D) (axisCost n D rho) (fun i hi => axisCost_le n D rho i hD hr
    (hi.trans_le (Nat.min_le_left _ _)))

/-- The full small-dimension executable has the same certified saving. Its
paid ordinal initialization, loop controls and final erasure are included. -/
theorem eventually_small_machine_cost (c m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, D≤d n → D≤CompactReservationGrowth.reserved c m n →
      (CompactFallbackOriginal.constant*CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n)*D : ℝ)≤
        η*(baseVolume n D : ℝ)*(d n : ℝ)^lam' := by
  have hs : (0:ℝ)<5*CompactFallbackOriginal.constant+1 := by positivity
  filter_upwards [CompactReservationRate.eventually_processed_certified c m hm
    (η/(5*CompactFallbackOriginal.constant+1)) (div_pos hη hs)] with n hn D hD hsmall
  have hc := hn D
  rw [(CompactReservationCutoff.fallback c m n D hsmall).1] at hc
  have hv : (CompactFallbackAxisRun.volume D (K n) (ℓ n) (precision n):ℝ)≤5*(baseVolume n D:ℝ) := by
    exact_mod_cast volume_le_base n D hD
  have hc' : (D:ℝ)≤(η*(d n:ℝ)^lam')/(5*CompactFallbackOriginal.constant+1) := by
    convert hc using 1; ring
  have he := (le_div_iff₀ hs).mp hc'
  calc
    _≤(CompactFallbackOriginal.constant:ℝ)*(5*(baseVolume n D:ℝ))*(D:ℝ) := by gcongr
    _≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
      have hscale := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) (baseVolume n D))
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) (d n)) lam']

end
end IntegerMultBounds.Machine.CompactFallbackActualBudget
