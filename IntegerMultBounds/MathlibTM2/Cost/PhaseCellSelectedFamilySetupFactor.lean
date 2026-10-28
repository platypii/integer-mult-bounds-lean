module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilySetupControls

/-! Only computed boundary factor construction remains outside the polynomial
price for the actual shared family setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedFamilySetup_factor_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        constructedBoundaryFactorCostBound p u l s t a b (boundaryRecoveryTarget p (target+1)) 2+
          C*t^2*p^4 := by
  obtain ⟨K,hK⟩ := selectedFamilySetup_construction_le ct
  obtain ⟨D,hD⟩ := selectedCouplingKeySetup_poly_le (1032+8*ct) 17
  refine ⟨K+D,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hwidth : 2*q+8 ≤ (1032+8*ct)*p := by
    convert hw using 1
    dsimp only [q,p,l,bits,N,band,s,t,executionPrecision,executionWidth]
    omega
  have hB : band ≤ 17*p := by
    have hsqrt := Nat.sqrt_le_self (16*p/u)
    have hdiv := Nat.div_le_self (16*p) u
    dsimp only [band,PhaseCellBand.width]
    omega
  have hc := hD n h i q u band a b hwidth hu hB hband ha hb
  have hs := hK n h i A u target a b hu htarget hband ha hb
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hscale := Nat.mul_le_mul_left (D*p^4) (show t ≤ t^2 by nlinarith only [ht])
  dsimp only [p,s,t,l,band,N,bits,q] at hc hscale ⊢
  dsimp only at hs
  nlinarith only [hc,hs,hscale]

end IntegerMultBounds.MathlibTM2.Cost
