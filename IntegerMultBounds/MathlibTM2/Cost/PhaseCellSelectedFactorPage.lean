module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFactorPagePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryWidths
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
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cR := 4*c+10
  refine ⟨20000000*cR^5,?_⟩
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
  let W := 12*band+1
  let R := cR*t
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have htR : t ≤ R := by dsimp only [R,cR]; nlinarith only [Nat.zero_le (c*t)]
  have hR : 1 ≤ R := ht.trans htR
  have hscale : c*p ≤ R := (Nat.mul_le_mul_left c hpt).trans
    (Nat.mul_le_mul_right t (by dsimp only [cR]; omega))
  have hwR : 2*q+8 ≤ R := (show 2*q+8 ≤ executionWidth p (haloInverseRingLog s t) (initialSchurTarget p u bits 2) 2 by
    dsimp only [q,executionPrecision,executionWidth]; omega).trans (hw.trans hscale)
  have hqR : q ≤ R := hq.trans hscale
  have hWR : W ≤ R := hW.trans hscale
  have hNR : N ≤ R := hN.trans htR
  have hWt : W ≤ c*t := hW.trans (Nat.mul_le_mul_left c hpt)
  have henv : N+2*W+2 ≤ R := by
    change N ≤ t at hN
    dsimp only [R,cR]
    nlinarith only [hN,hWt,ht,Nat.zero_le (c*t)]
  have hf := factorPageCost_poly hR hqR hWR hNR hwR henv
  have hBR : band ≤ R := hB.trans hscale
  have hp5 : R ≤ R^5 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 5 by decide)
  have hcost : generatedFactorPageCost q band N ≤ 20000000*R^5 := by
    dsimp only [generatedFactorPageCost]
    change _ ≤ _
    nlinarith only [hf,hBR,hWR,hR,hp5]
  simpa only [R,t,mul_pow,Nat.mul_assoc] using hcost

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
