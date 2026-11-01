module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Shared mask generation has a polynomial setup bill, independent of the replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem initializeRecoveryMasksCost_le (V N band : ℕ) :
    initializeRecoveryMasksCost V N band ≤ 10000*(N+band+1)*(V+5)^2 := by
  unfold initializeRecoveryMasksCost tblC
  nlinarith only [Nat.zero_le (N*V), Nat.zero_le (band*V),
    Nat.zero_le (N*V^2), Nat.zero_le (band*V^2), Nat.zero_le (V^2)]

/-- The shared mask bill fits the existing polynomial core-setup allowance. -/
theorem initializeRecoveryMasksCost_core_le {V N band t p : ℕ} (cV : ℕ)
    (hN : N ≤ t) (hband : band ≤ t) (ht : 1 ≤ t) (hp : 1 ≤ p) (hV : V ≤ cV*p) :
    initializeRecoveryMasksCost V N band ≤ 30000*(cV+5)^2*(t^6*p^4) := by
  have hrows : N+band+1 ≤ 3*t := by omega
  have hwidth : V+5 ≤ (cV+5)*p := by nlinarith only [hV,hp]
  have ht6 : t ≤ t^6 := Nat.le_self_pow (by decide) t
  have hp4 : p^2 ≤ p^4 := Nat.pow_le_pow_right hp (by decide)
  calc
    _ ≤ 10000*(N+band+1)*(V+5)^2 := initializeRecoveryMasksCost_le V N band
    _ ≤ 10000*(3*t)*((cV+5)*p)^2 := by gcongr
    _ = 30000*(cV+5)^2*(t*p^2) := by ring
    _ ≤ 30000*(cV+5)^2*(t^6*p^4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul ht6 hp4)

/-- One mask initialization per selected core fits below the whole-box volume.
Counting distinct cores remains a separate scheduling obligation. -/
theorem selectedInitializeRecoveryMasksCost_volume_le (cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ V N band : ℕ, N ≤ Sizes.t n i → band ≤ Sizes.t n i → V ≤ cV*Sizes.p n →
      scale*initializeRecoveryMasksCost V N band ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (scale*(30000*(cV+5)^2)) 4 6] with n hn
  intro h i V N band hN hband hV
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hc := initializeRecoveryMasksCost_core_le cV hN hband ht hp hV
  apply (Nat.mul_le_mul_left scale hc).trans
  convert hn i using 1; ring

end IntegerMultBounds.MathlibTM2.Cost
