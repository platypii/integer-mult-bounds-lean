module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedUncachedCoupling
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSchurColumnControlCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSchurTableFormatting

/-! Computed Schur-column construction pays one actual interior solve; both
uncached coupling passes and all column controls have polynomial prices. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedIndexedSchurColumn_interior_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      retainedIndexedColumnCost p u l s t a b bits N s ≤
        solveHaloInteriorCost p l s t u stage 2 a b+C*t^5 := by
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  obtain ⟨D,hD⟩ := selectedBorrowedCouplingPass_poly_le c
  let B := 1000000*(2^15+c+10)*(2*c+1)
  refine ⟨2*D+B,?_⟩
  intro n h i _ u target a b hu htarget hband ha hb
  dsimp only
  obtain ⟨hpt,hN,hq,hw,hV,hW,hB⟩ := hwidths n h i u target a b htarget hband
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  let V := publicationGeometryWidth t band
  let H := 2^15*p+q+s+t+u+band+a+b+N+s+1
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hwq : w = 2*q+8 := by dsimp only [w,q,executionWidth,executionPrecision]; omega
  have hw' : 2*q+8 ≤ c*p := by rw [← hwq]; exact hw
  have htrue := hD n h i q u band a b hw' hu hband ha hb true
  have hfalse := hD n h i q u band a b hw' hu hband ha hb false
  rw [← hwq] at htrue hfalse
  have hqt : q ≤ c*t := hq.trans (Nat.mul_le_mul_left c hpt)
  have hP := Nat.mul_le_mul_left (2^15) hpt
  have hH : H ≤ (2^15+c+10)*t := by
    change N ≤ t at hN
    dsimp only [H]
    change u ≤ p at hu
    change band ≤ s at hband
    change a ≤ s at ha
    change b ≤ s at hb
    change p ≤ t at hpt
    nlinarith only [hP,hqt,hst,hu,hband,ha,hb,hN,hpt,ht]
  have hR : V+w+1 ≤ (2*c+1)*t := by
    have hcp := Nat.mul_le_mul_left c hpt
    change V ≤ c*p at hV
    change w ≤ c*p at hw
    change p ≤ t at hpt
    nlinarith only [hV,hw,hcp,ht]
  have hprod := Nat.mul_le_mul hH hR
  have hformat₀ : 1000000*H*(V+w+1) ≤ B*t^2 := by
    dsimp only [B]
    nlinarith only [hprod]
  have hformat := hformat₀.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_right ht (show 2 ≤ 5 by decide)))
  have hcost := retainedIndexedColumnCost_controls_le p u l s t a b bits N s
  change retainedIndexedColumnCost p u l s t a b bits N s ≤
    solveHaloInteriorCost p l s t u stage 2 a b+
      borrowedCouplingPassCost true (2^15*p) q w s t u band a b+
      borrowedCouplingPassCost false (2^15*p) q w s t u band a b+1000000*H*(V+w+1) at hcost
  dsimp only [p,s,t,l,band,N,bits,stage,q,w,V,H] at hcost htrue hfalse hformat ⊢
  nlinarith only [hcost,htrue,hfalse,hformat]

theorem selectedFamilySetup_interiorConstruction_le (ct : ℕ) :
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
      let stage := initialSchurTarget p u bits 2
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        N*solveHaloInteriorCost p l s t u stage 2 a b+C*t^6*p^4 := by
  obtain ⟨K,hK⟩ := selectedFamilySetup_columns_le ct
  obtain ⟨D,hD⟩ := selectedIndexedSchurColumn_interior_le ct
  refine ⟨K+D,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  have hs := hK n h i A u target a b hu htarget hband ha hb
  have hd := hD n h i u target a b hu htarget hband ha hb
  dsimp only at hs hd
  let N := (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card
  have hN : N ≤ Sizes.t n i :=
    (show N ≤ Sizes.s n i by simpa [N] using (haloBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a b).card_le_univ).trans (h.good.lt i).le
  have hprod := Nat.mul_le_mul_left N hd
  have hcharge := Nat.mul_le_mul_right (D*(Sizes.t n i)^5) hN
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hscale := Nat.mul_le_mul_left (D*(Sizes.t n i)^6) (Nat.one_le_pow 4 (Sizes.p n) hp)
  dsimp only [N] at hprod hcharge
  nlinarith only [hs,hprod,hcharge,hscale]

end IntegerMultBounds.MathlibTM2.Cost
