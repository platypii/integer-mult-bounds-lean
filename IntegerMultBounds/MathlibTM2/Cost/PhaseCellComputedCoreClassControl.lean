module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassControlCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareComputedCoreClass

/-! Class preparation, scan control and final counter retirement are paid once
per class plus linear local replica traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def computedClassControlTime (V s width radius H W N : ℕ) : ℕ :=
  preparedCoreOriginsCost V s width radius H+H*(6*W+9)+7*(coreGatherIndices s width radius H).length+19+
    N*(6*(H*W)+9)

theorem computedClassTimeBill_eq (V s width radius H W N coreTime : ℕ) :
    (preparedCoreOriginsCost V s width radius H+recoveryPayloadCountCost N H W)+
      (coreTime+5*(coreGatherIndices s width radius H).length+4)+
      (2*((coreGatherIndices s width radius H).length+N*(H*W))+5) =
        coreTime+computedClassControlTime V s width radius H W N := by
  unfold computedClassControlTime recoveryPayloadCountCost
  ring

theorem selectedComputedClassControlTime_le (cB cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (V width radius H W N band : ℕ),
      0 < width → V ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n → H ≤ Sizes.s n i →
      (computedClassControlTime V (Sizes.s n i) width radius H W N : ℝ) ≤
        Sizes.T n+(6*cW+9 : ℕ)*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hOrigins⟩ := selectedCoreOriginsCost_poly_le cB
  filter_upwards [selectedAxisPolynomial_le_volume (C+6*cW+35) 0 3] with n hpoly
  intro h i V width radius H W N band hw hV hW hH
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have ht1 : 1 ≤ Sizes.t n i := hp1.trans hpt
  have hst := Nat.le_of_lt (h.good.lt i)
  have hHt := hH.trans hst
  have hWt := hW.trans (Nat.mul_le_mul_left cW hpt)
  have hJ := (coreGatherIndices_length_le (Sizes.s n i) width radius H hw).trans hst
  have hOrigins := hOrigins n h i V width radius H hw hV
  have hrow := Nat.mul_le_mul hHt (show 6*W+9 ≤ 6*(cW*Sizes.t n i)+9 by omega)
  have ht23 : (Sizes.t n i)^2 ≤ (Sizes.t n i)^3 := Nat.pow_le_pow_right ht1 (by decide)
  have ht13 : Sizes.t n i ≤ (Sizes.t n i)^3 := Nat.le_self_pow (by decide) _
  have hunit : 1 ≤ (Sizes.t n i)^3 := ht1.trans ht13
  have hscaled := Nat.mul_le_mul_left (6*cW) ht23
  have hfixed : preparedCoreOriginsCost V (Sizes.s n i) width radius H+H*(6*W+9)+
      7*(coreGatherIndices (Sizes.s n i) width radius H).length+19 ≤ Sizes.T n := by
    have hb : preparedCoreOriginsCost V (Sizes.s n i) width radius H+H*(6*W+9)+
        7*(coreGatherIndices (Sizes.s n i) width radius H).length+19 ≤ (C+6*cW+35)*(Sizes.t n i)^3 := by
      nlinarith only [hOrigins,hrow,hJ,hscaled,ht13,hunit]
    exact hb.trans (by simpa only [pow_zero,Nat.mul_one] using hpoly i)
  have hHW : H*W ≤ cW*Sizes.t n i*Sizes.p n := by
    have hm := Nat.mul_le_mul hHt hW
    nlinarith only [hm]
  have htp : 1 ≤ Sizes.t n i*Sizes.p n := Nat.mul_pos ht1 hp1
  have hrep : N*(6*(H*W)+9) ≤ (6*cW+9)*N*Sizes.t n i*Sizes.p n := by
    have hm := Nat.mul_le_mul_left N (show 6*(H*W)+9 ≤ (6*cW+9)*Sizes.t n i*Sizes.p n by
      nlinarith only [hHW,htp])
    nlinarith only [hm]
  have hpR : (1 : ℝ) ≤ Sizes.p n := by exact_mod_cast hp1
  have hpPow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hnonneg : (0 : ℝ) ≤ (band : ℝ)^2/Sizes.d n := by positivity
  have htR : (Sizes.t n i : ℝ) ≤ (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n) := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (Sizes.t n i) : (0 : ℝ) ≤ Sizes.t n i) hnonneg]
  have hlinear := mul_le_mul htR hpPow (by positivity)
    (by positivity : (0 : ℝ) ≤ (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n))
  have hlin := mul_le_mul_of_nonneg_left hlinear (by positivity : (0 : ℝ) ≤ (6*cW+9 : ℕ)*N)
  have hfixedR := (Nat.cast_le (α := ℝ)).mpr hfixed
  have hrepR := (Nat.cast_le (α := ℝ)).mpr hrep
  unfold computedClassControlTime
  push_cast at hfixedR hrepR hlin ⊢
  nlinarith only [hfixedR,hrepR,hlin]

end IntegerMultBounds.MathlibTM2.Cost
