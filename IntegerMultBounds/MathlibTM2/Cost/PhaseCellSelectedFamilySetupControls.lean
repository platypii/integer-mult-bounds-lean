module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundarySetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilySetupWeight

/-! The actual family setup is reduced to numerical factor/coupling construction
plus a proved quadratic-axis, quartic-precision control and weight bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedFamilySetup_construction_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let solveTarget := boundaryRecoveryTarget p (target+1)
      let bits := boundaryTableBits p solveTarget 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        constructedBoundaryFactorCostBound p u l s t a b solveTarget 2+
        couplingKeySetupCost (2^15*p) q s t u band a b+C*t^2*p^4 := by
  let cw := 1032+8*ct
  let cZ := cw+33000
  obtain ⟨K,hK⟩ := selectedFamilySetup_weight_le ct
  refine ⟨K+1002000*cZ^3+6*cw+30,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  let V := publicationGeometryWidth t band
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ,cw]; nlinarith only [hp]
  have hbandP : band ≤ 17*p := by
    have hsqrt := Nat.sqrt_le_self (16*p/u)
    have hdiv := Nat.div_le_self (16*p) u
    dsimp only [band,PhaseCellBand.width]
    omega
  have hWP : W ≤ 205*p := by dsimp only [W]; omega
  have hbitsT : Nat.size t ≤ p+1 := by
    have htbits := selectedAxisBits_le n i
    have hell := selectedAxisLog_le_precision h
    dsimp only [p,t] at *
    omega
  have hbitsB : Nat.size band ≤ p+1 := (Nat.size_le_size (hband.trans hst.le)).trans hbitsT
  have hVP : V ≤ 15*p := by dsimp only [V,publicationGeometryWidth]; omega
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  change w ≤ cw*p at hw
  have hwZ : w ≤ Z := hw.trans (Nat.mul_le_mul_right p (by dsimp only [cZ,cw]; omega))
  have hWZ : W ≤ Z := hWP.trans (Nat.mul_le_mul_right p (by dsimp only [cZ,cw]; omega))
  have hVZ : V ≤ Z := hVP.trans (Nat.mul_le_mul_right p (by dsimp only [cZ,cw]; omega))
  have hqZ : q ≤ Z := (show q ≤ w by dsimp only [q,w,executionPrecision,executionWidth]; omega).trans hwZ
  have hqw : 2*q+8 = w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hN : N ≤ t := (show N ≤ s by simpa [N] using (haloBoundary s t band a b).card_le_univ).trans hst.le
  have hperm := boundaryPermanentSizeBound_poly ht hZ hN hqZ (by rw [hqw]; exact hwZ) hWZ
  have hH : 12*band*w+N*W ≤ Z^2+t*Z := by
    have hp₁ := Nat.mul_le_mul (show 12*band ≤ Z by dsimp only [W] at hWZ; omega) hwZ
    have hp₂ := Nat.mul_le_mul hN hWZ
    nlinarith only [hp₁,hp₂]
  have hrelease := placedFactorBatchReleaseCostBound_zero_poly ht hZ hst.le hN hWZ hwZ hVZ hperm hH
  have hpub := sharedPagePublicationSetupCost_poly ht hZ hN hst.le hVZ hwZ
  have hZ3 : Z ≤ Z^3 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 3 by decide)
  have hpubscale := Nat.mul_le_mul_left (1000*t^2) hZ3
  have hPZ : 2^15*p ≤ Z := Nat.mul_le_mul_right p (by dsimp only [cZ,cw]; omega)
  have huZ : u ≤ Z := hu.trans (by dsimp only [Z,cZ,cw]; nlinarith only [Nat.zero_le p])
  have hbZ : band ≤ Z := hbandP.trans (Nat.mul_le_mul_right p (by dsimp only [cZ,cw]; omega))
  have hcrelease := couplingKeyReleaseCost_poly ht hZ hst.le hPZ hqZ huZ hbZ
    (ha.trans hst.le) (hb.trans hst.le) (by rw [hqw]; exact hwZ)
  have hrelscale := Nat.mul_le_mul (show t ≤ t^2 by nlinarith only [ht])
    (show Z^2 ≤ Z^3 by exact Nat.pow_le_pow_right hZ (by decide))
  have hfamily := hK n h i A u target a b hu htarget hband ha hb
  have hmovement : s*(4*w+9)+2*s*w+16 ≤ (6*cw+25)*t*p := by
    have hv := Nat.mul_le_mul hst.le hw
    have htp := Nat.mul_le_mul_left t hp
    nlinarith only [hv,htp,ht,hst]
  have hp34 : p^3 ≤ p^4 := by nlinarith only [Nat.mul_le_mul_left (p^3) hp]
  have hp1 : p ≤ p^4 := by simpa using Nat.pow_le_pow_right hp (show 1 ≤ 4 by decide)
  have htt : t ≤ t^2 := by nlinarith only [ht]
  have hweight := Nat.mul_le_mul_left (K*p^4) htt
  have hcontrols := Nat.mul_le_mul_left (1002000*cZ^3*t^2) hp34
  have hmove := Nat.mul_le_mul (Nat.mul_le_mul_left (6*cw+25) htt) hp1
  dsimp only [generatedComplexSetupCostBound] at hfamily
  dsimp only [p,s,t,l,band,N,solveTarget,bits,q,w,W,V,Z] at hfamily hrelease hpub hpubscale hcrelease hrelscale hmovement hweight hcontrols hmove ⊢
  nlinarith only [hfamily,hrelease,hpub,hpubscale,hcrelease,hrelscale,hmovement,hweight,hcontrols,hmove]

end IntegerMultBounds.MathlibTM2.Cost
