module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedWeightSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyBatchGeometryCost

/-! Price the numerical family construction and final erasure in the actual
shared setup ledger, at the precision used by the boundary/recovery caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedFamilySetup_weight_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      generatedFamilyComplexSetupCostBound A p u l s t a b target ≤
        generatedComplexSetupCostBound p u l s t a b target+C*t*p^4 := by
  let cw := 1032+8*ct
  obtain ⟨C,hC⟩ := selectedWeightFamilySetup_poly_le cw 20
  refine ⟨C+8*cw+14,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
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
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hqw : 2*q+8 = w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hcount : executionStagePrecision p l stage 2+1 ≤ w := by
    dsimp only [w,executionWidth,executionStagePrecision]; omega
  obtain ⟨hl,_⟩ := haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)
  have hfamily := hC n h i A (executionStagePrecision p l stage 2+1) q l u band a b
    (hcount.trans hw) (by rw [hqw]; exact hw) hl hu hband ha hb
  have hp4 : p ≤ p^4 := by simpa using Nat.pow_le_pow_right hp (show 1 ≤ 4 by decide)
  have hprod := Nat.mul_le_mul hst.le hw
  have hscale := Nat.mul_le_mul_left (cw*t) hp4
  have hone : 1 ≤ t*p^4 := by simpa using Nat.mul_le_mul ht (Nat.one_le_pow 4 p hp)
  dsimp only [generatedFamilyComplexSetupCostBound]
  change _ ≤ _
  dsimp only [p,s,t,l,band,N,bits,stage,q,w,cw] at hfamily hprod hscale hone ⊢
  nlinarith only [hfamily,hprod,hscale,hone]

end IntegerMultBounds.MathlibTM2.Cost
