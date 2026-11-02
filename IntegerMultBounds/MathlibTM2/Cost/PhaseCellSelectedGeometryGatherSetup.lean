module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassControlCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Complete origin generation and fifth-degree metadata setup are paid by the
selected global volume, once per class and independently of replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN

theorem selectedGeometryGatherSetup_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V width radius L : ℕ),
    0 < width → V ≤ cV*Sizes.p n →
    (2*preparedCoreOriginsCost V (Sizes.s n i) width radius L+204+
      2*(116*V+143+32921*(V+1)^5) ≤ Sizes.T n) ∧
    ((342*V+423+98763*(V+1)^5)+4*preparedCoreOriginsCost V (Sizes.s n i) width radius L+300 ≤ Sizes.T n) := by
  obtain ⟨C,hOrigins⟩ := selectedCoreOriginsCost_poly_le cV
  let coefficient := 6*C+574*cV+1213+164605*(cV+1)^5
  filter_upwards [selectedAxisPolynomial_le_volume coefficient 0 5] with n hpoly
  intro h i V width radius L hw hV
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have ht : 1 ≤ Sizes.t n i := hp.trans hpt
  have ht15 : Sizes.t n i ≤ Sizes.t n i^5 := Nat.le_self_pow (by decide) _
  have ht35 : Sizes.t n i^3 ≤ Sizes.t n i^5 := Nat.pow_le_pow_right ht (by decide)
  have hunit : 1 ≤ Sizes.t n i^5 := ht.trans ht15
  have hO := (hOrigins n h i V width radius L hw hV).trans (Nat.mul_le_mul_left C ht35)
  have hVt : V ≤ cV*Sizes.t n i := hV.trans (Nat.mul_le_mul_left cV hpt)
  have hV5 := hVt.trans (Nat.mul_le_mul_left cV ht15)
  have hbase : V+1 ≤ (cV+1)*Sizes.t n i := by nlinarith only [hVt,ht]
  have hpow := Nat.pow_le_pow_left hbase 5
  rw [Nat.mul_pow] at hpow
  have hsum : (2*preparedCoreOriginsCost V (Sizes.s n i) width radius L+204+
      2*(116*V+143+32921*(V+1)^5))+
      ((342*V+423+98763*(V+1)^5)+4*preparedCoreOriginsCost V (Sizes.s n i) width radius L+300) ≤
      coefficient*Sizes.t n i^5 := by
    dsimp only [coefficient]
    nlinarith only [hO,hV5,hpow,hunit]
  have hbound : coefficient*Sizes.t n i^5 ≤ Sizes.T n := by
    simpa only [pow_zero,Nat.mul_one] using hpoly i
  have hh := hsum.trans hbound
  exact ⟨(Nat.le_add_right _ _).trans hh,(Nat.le_add_left _ _).trans hh⟩

end IntegerMultBounds.MathlibTM2.Cost
