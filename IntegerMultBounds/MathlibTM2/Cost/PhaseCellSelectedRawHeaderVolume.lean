module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Any fixed multiple of the selected raw-header work fits below box volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedRawHeaderCost_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let W := inverseCallerWordWidth p u l target s t
      scale*(inverseScalarAtoms p s t u 0 s*tblC W 0+
        inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
        inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)) ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume
    (scale*20000*100000^3*(ct+21)^6) 0 6] with n hn
  intro h i _ u target hu htarget hband
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let Z := (ct+21)*t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have htZ : t ≤ Z := Nat.le_mul_of_pos_left t (by omega)
  have hZ : 1 ≤ Z := (hp.trans hpt).trans htZ
  have hpZ := hpt.trans htZ
  have huZ := hu.trans hpZ
  have hsZ := hst.le.trans htZ
  have hl := (haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)).1
  have hlZ : l ≤ Z := hl.trans ((Nat.mul_le_mul_left 20 hpt).trans
    (Nat.mul_le_mul_right t (by omega : 20 ≤ ct+21)))
  have htargetZ : target ≤ Z := htarget.trans ((Nat.mul_le_mul_left ct hpt).trans
    (Nat.mul_le_mul_right t (by omega : ct ≤ ct+21)))
  have hb := inverseCallerHeaders_poly hZ hpZ huZ hlZ htargetZ hsZ htZ (hband.trans hsZ)
  have hc := Nat.mul_le_mul_left scale hb
  have hv := hn i
  simp only [pow_zero,mul_one] at hv
  exact hc.trans (by convert hv using 1 <;> dsimp only [Z] <;> ring)

end IntegerMultBounds.MathlibTM2.Cost
