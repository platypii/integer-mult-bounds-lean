module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedCouplingPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingSetup

/-! The uncached coefficient-producing coupling path used during table
construction has a uniform selected polynomial price for both source masks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedBorrowedCouplingPass_poly_le (cw : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u band a b : ℕ),
      2*q+8 ≤ cw*Sizes.p n → u ≤ Sizes.p n → band ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i → ∀ boundary : Bool,
      borrowedCouplingPassCost boundary (2^15*Sizes.p n) q (2*q+8)
        (Sizes.s n i) (Sizes.t n i) u band a b ≤ C*(Sizes.t n i)^5 := by
  let cR := 3*cw+500000
  let D := 10000000*(ssMulConst+1)*cR^5
  obtain ⟨K,hK⟩ := selectedMasks_fast_le
  refine ⟨K+D,?_⟩
  intro n h i q u band a b hw hu hband ha hb boundary
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let R := cR*t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have htR : t ≤ R := by dsimp only [R,cR]; nlinarith only [Nat.zero_le (cw*t)]
  have hR : 1 ≤ R := ht.trans htR
  have hscale (c : ℕ) (hc : c ≤ cR) : c*p ≤ R :=
    (Nat.mul_le_mul_left c hpt).trans (Nat.mul_le_mul_right t hc)
  have hP := hscale (2^15) (by dsimp only [cR]; omega)
  have hwR := hw.trans (hscale cw (by dsimp only [cR]; omega))
  have hqR : q ≤ R := (show q ≤ 2*q+8 by omega).trans hwR
  have huR : u ≤ R := hu.trans (hpt.trans htR)
  have hbR : band ≤ R := hband.trans (hst.le.trans htR)
  have hv := selectedLiftedCoefficientWidth_le cw h i q (2*q+8) u band hw (by omega) hu hband
  have hVR := hv.trans (hscale (2*cw+426064) (by dsimp only [cR]; omega))
  have hcost := borrowedCouplingPassCost_poly (a := a) (b := b) hR ht hst.le htR hP hqR hwR (by omega) huR hbR hVR boundary
  have hmask := hK n h i band a b hband ha hb
  have htp : t*p ≤ t^2 := by nlinarith only [Nat.mul_le_mul_left t hpt]
  have hp5 : t^2 ≤ t^5 := Nat.pow_le_pow_right ht (by decide)
  have hmaskScale := Nat.mul_le_mul_left K (htp.trans hp5)
  dsimp only [prepareCouplingGuardCost,R,p,s,t] at hcost hmaskScale ⊢
  dsimp only [D]
  nlinarith only [hcost,hmask,hmaskScale]

end IntegerMultBounds.MathlibTM2.Cost
