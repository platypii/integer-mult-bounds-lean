module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFactorPagePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilySetupFactor

/-! Price factor-page assembly at the actual selected dimensions. Computation of
the Schur columns and numerical factor arithmetic remain separately charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedGeneratedFactorPage_poly_le (ct : ℕ) :
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
      generatedFactorPageCost q band N ≤ C*t^5 := by
  let cw := 1032+8*ct
  let cR := 2*cw+500
  refine ⟨20000000*cR^5,?_⟩
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
  let W := 12*band+1
  let R := cR*t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have hR : 1 ≤ R := by dsimp only [R,cR,cw]; nlinarith only [ht]
  have hB : band ≤ 17*p := by
    have hsqrt := Nat.sqrt_le_self (16*p/u)
    have hdiv := Nat.div_le_self (16*p) u
    dsimp only [band,PhaseCellBand.width]
    omega
  have hW : W ≤ 205*p := by dsimp only [W]; omega
  have hN : N ≤ t := (show N ≤ s by simpa [N] using (haloBoundary s t band a b).card_le_univ).trans hst.le
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hwidth : 2*q+8 ≤ cw*p := by
    convert hw using 1
    dsimp only [q,p,l,bits,N,band,s,t,executionPrecision,executionWidth]
    omega
  have hwR : 2*q+8 ≤ R := hwidth.trans ((Nat.mul_le_mul_left cw hpt).trans
    (Nat.mul_le_mul_right t (by dsimp only [cR]; omega)))
  have hqR : q ≤ R := (show q ≤ 2*q+8 by omega).trans hwR
  have hWR : W ≤ R := hW.trans ((Nat.mul_le_mul_left 205 hpt).trans
    (Nat.mul_le_mul_right t (by dsimp only [cR,cw]; omega)))
  have hNR : N ≤ R := hN.trans (by dsimp only [R,cR,cw]; nlinarith only [Nat.zero_le t])
  have henv : N+2*W+2 ≤ R := by
    have hWt := hW.trans (Nat.mul_le_mul_left 205 hpt)
    dsimp only [R,cR,cw]
    nlinarith only [hN,hWt,ht,Nat.zero_le (ct*t)]
  have hc := factorPageCost_poly hR hqR hWR hNR hwR henv
  have hBR : band ≤ R := (show band ≤ W by dsimp only [W]; omega).trans hWR
  have hp5 : R ≤ R^5 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 5 by decide)
  have hcost : generatedFactorPageCost q band N ≤ 20000000*R^5 := by
    dsimp only [generatedFactorPageCost]
    change _ ≤ _
    nlinarith only [hc,hBR,hWR,hR,hp5]
  simpa only [R,mul_pow,Nat.mul_assoc] using hcost

theorem selectedFamilySetup_factorArithmetic_le (ct : ℕ) :
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
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        constructedBoundaryTableCostBound p u l s t a b bits+boundaryFactorSetupCost p q band N+
          bandAxisPrepCost w (12*band) (factorNewtonSteps p q) N+C*t^5*p^4 := by
  obtain ⟨K,hK⟩ := selectedFamilySetup_factor_le ct
  obtain ⟨D,hD⟩ := selectedGeneratedFactorPage_poly_le ct
  refine ⟨K+D,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  have hs := hK n h i A u target a b hu htarget hband ha hb
  have hd := hD n h i u target a b htarget hband
  dsimp only at hs hd
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht25 : (Sizes.t n i)^2 ≤ (Sizes.t n i)^5 := Nat.pow_le_pow_right ht (by decide)
  have hscale := Nat.mul_le_mul_left (K*(Sizes.p n)^4) ht25
  have hp4 : 1 ≤ (Sizes.p n)^4 := Nat.one_le_pow 4 _ hp
  have hDscale := Nat.mul_le_mul_left (D*(Sizes.t n i)^5) hp4
  dsimp only [constructedBoundaryFactorCostBound] at hs
  nlinarith only [hs,hd,hscale,hDscale]

end IntegerMultBounds.MathlibTM2.Cost
