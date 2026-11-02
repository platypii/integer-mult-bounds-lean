module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreWidths
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassInputValues
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Shared class-input ticks are a setup charge plus the replica count.
The retained binary dimension width remains an explicit linear charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  ComputedClassBanks

theorem selectedCommonInputCost_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (u target B W N radius H D : ℕ),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      B ≤ (2*(ct+21)+22)*Sizes.p n → W ≤ (1032+8*ct)*Sizes.p n →
      radius ≤ Sizes.s n i → H ≤ Sizes.s n i →
      165*D+8*inputVolume (commonInputValues (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i)
        B W N radius H)+122 ≤ Sizes.T n+165*D+8*N := by
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  let cV := 100+ct+3*cB+cW
  filter_upwards [selectedAxisPolynomial_le_volume (8*cV+122) 0 1] with n hn
  intro h i u target B W N radius H D hu htarget hB hW hradius hH
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have hst := Nat.le_of_lt (h.good.lt i)
  have ht1 : 1 ≤ Sizes.t n i := hp1.trans hpt
  have hlc := (haloInverseRingLog_bounds hp1 (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hu' := hu.trans hpt
  have htarget' := htarget.trans (Nat.mul_le_mul_left ct hpt)
  have hB' := hB.trans (Nat.mul_le_mul_left cB hpt)
  have hW' := hW.trans (Nat.mul_le_mul_left cW hpt)
  have hradius' := hradius.trans hst
  have hH' := hH.trans hst
  have hvolume : inputVolume (commonInputValues (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.s n i) (Sizes.t n i)
      B W N radius H) ≤ cV*Sizes.t n i+N := by
    rw [commonInputVolume_eq]
    dsimp only [cV]
    nlinarith only [hpt,hu',hlc,htarget',hB',hW',hradius',hH',hst,
      Nat.mul_le_mul_left 20 hpt,Nat.sub_le H (2*radius)]
  have hfixed : 8*cV*Sizes.t n i+122 ≤ Sizes.T n := by
    have hh := hn i
    simp only [pow_zero,pow_one,Nat.mul_one] at hh
    nlinarith only [hh,ht1]
  nlinarith only [hvolume,hfixed]

end IntegerMultBounds.MathlibTM2.Cost
