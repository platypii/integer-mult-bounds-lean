module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryFactorSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFactorPage

/-! Numerical boundary-factor preparation is paid at the actual selected caller
precision, leaving only computed Schur columns in the shared setup bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedBoundaryFactorPreparation_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, target ≤ ct*Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      boundaryFactorSetupCost p q band N+
          bandAxisPrepCost (2*q+8) (12*band) (factorNewtonSteps p q) N ≤ C*t^6 := by
  let cw := 1032+8*ct
  let cR := 2*cw+400
  let B := 1000000+10000000*(ssMulConst+1)
  refine ⟨B*cR^6,?_⟩
  intro n h i _ u target a b htarget hband
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hB : band ≤ 17*p := by
    have hsqrt := Nat.sqrt_le_self (16*p/u)
    have hdiv := Nat.div_le_self (16*p) u
    dsimp only [band,PhaseCellBand.width]
    omega
  have hN : N ≤ t := (show N ≤ s by simpa [N] using (haloBoundary s t band a b).card_le_univ).trans hst.le
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hwidth : 2*q+8 ≤ cw*p := by
    convert hw using 1
    dsimp only [q,p,l,bits,N,band,s,t,executionPrecision,executionWidth]
    omega
  have hq : q ≤ cw*t := (show q ≤ 2*q+8 by omega).trans
    (hwidth.trans (Nat.mul_le_mul_left cw hpt))
  have hb : band ≤ 17*t := hB.trans (Nat.mul_le_mul_left 17 hpt)
  have hR : p+2*q+12*band+N+100 ≤ cR*t := by
    dsimp only [cR]
    nlinarith only [hpt,hq,hb,hN,ht]
  have hc := boundaryFactorPreparationCost_poly p q band N
  have hpower := Nat.pow_le_pow_left hR 6
  have hbound := hc.trans (Nat.mul_le_mul_left B hpower)
  simpa only [mul_pow,Nat.mul_assoc] using hbound

theorem selectedFamilySetup_table_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        constructedBoundaryTableCostBound p u l s t a b bits+C*t^6*p^4 := by
  obtain ⟨K,hK⟩ := selectedFamilySetup_factorArithmetic_le ct
  obtain ⟨D,hD⟩ := selectedBoundaryFactorPreparation_poly_le ct
  refine ⟨K+D,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  have hs := hK n h i A u target a b hu htarget hband ha hb
  have hd := hD n h i u target a b htarget hband
  dsimp only at hs hd
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have ht56 : (Sizes.t n i)^5 ≤ (Sizes.t n i)^6 := Nat.pow_le_pow_right ht (by decide)
  have hscale := Nat.mul_le_mul_left (K*(Sizes.p n)^4) ht56
  have hDscale := Nat.mul_le_mul_left (D*(Sizes.t n i)^6) (Nat.one_le_pow 4 (Sizes.p n) hp)
  have heq : ∀ p l target, executionWidth p l target 2 = 2*executionPrecision p l target 2+8 := by
    intro p l target
    dsimp only [executionWidth,executionPrecision]
    omega
  simp only [heq] at hs
  nlinarith only [hs,hd,hscale,hDscale]

end IntegerMultBounds.MathlibTM2.Cost
