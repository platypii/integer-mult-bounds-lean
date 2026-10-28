module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryFactorSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFactorPage
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryWidths

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
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cR := 14*c+102
  let B := 1000000+10000000*(ssMulConst+1)
  refine ⟨B*cR^6,?_⟩
  intro n h i _ u target a b htarget hband
  dsimp only
  obtain ⟨hpt,hN,hq,hw,hV,hW,hB⟩ := hwidths n h i u target a b htarget hband
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p (haloInverseRingLog s t) (initialSchurTarget p u bits 2) 2
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hqt : q ≤ c*t := hq.trans (Nat.mul_le_mul_left c hpt)
  have hbt : band ≤ c*t := hB.trans (Nat.mul_le_mul_left c hpt)
  have hR : p+2*q+12*band+N+100 ≤ cR*t := by
    change p ≤ t at hpt
    change N ≤ t at hN
    dsimp only [cR]
    nlinarith only [hpt,hqt,hbt,hN,ht]
  have hprep := boundaryFactorPreparationCost_poly p q band N
  have hpower := Nat.pow_le_pow_left hR 6
  have hbound := hprep.trans (Nat.mul_le_mul_left B hpower)
  simpa only [t,mul_pow,Nat.mul_assoc] using hbound

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
