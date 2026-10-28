module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization

/-! One uniform envelope for the actual inverse boundary bank's numerical and
geometry widths, shared by setup-cost specializations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedInverseBoundaryWidths_le (ct : ℕ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, target ≤ ct*Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      p ≤ t ∧ N ≤ t ∧ q ≤ c*p ∧ w ≤ c*p ∧ publicationGeometryWidth t band ≤ c*p ∧
        12*band+1 ≤ c*p ∧ band ≤ c*p := by
  let c := 1032+8*ct+220
  refine ⟨c,by dsimp only [c]; omega,?_⟩
  intro n h i _ u target a b htarget hband
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let band := PhaseCellBand.width p u
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hB : band ≤ 17*p := by
    have hsqrt := Nat.sqrt_le_self (16*p/u)
    have hdiv := Nat.div_le_self (16*p) u
    dsimp only [band,PhaseCellBand.width]
    omega
  have hW : 12*band+1 ≤ 205*p := by omega
  have hbitsT : Nat.size t ≤ p+1 := by
    have htbits := selectedAxisBits_le n i
    have hell := selectedAxisLog_le_precision h
    dsimp only [p,t] at *
    omega
  have hbitsB : Nat.size band ≤ p+1 := (Nat.size_le_size (hband.trans hst.le)).trans hbitsT
  have hV : publicationGeometryWidth t band ≤ 15*p := by
    dsimp only [publicationGeometryWidth]; omega
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hw' := hw.trans (Nat.mul_le_mul_right p (by dsimp only [c]; omega : 1032+8*ct ≤ c))
  refine ⟨selectedPrecision_le_axis h i,
    (show (haloBoundary s t band a b).card ≤ s by simpa using (haloBoundary s t band a b).card_le_univ).trans hst.le,
    ?_,hw',?_,?_,?_⟩
  · exact (show executionPrecision _ _ _ _ ≤ executionWidth _ _ _ _ by
      dsimp only [executionPrecision,executionWidth]; omega).trans hw'
  · exact hV.trans (Nat.mul_le_mul_right p (by dsimp only [c]; omega))
  · exact hW.trans (Nat.mul_le_mul_right p (by dsimp only [c]; omega))
  · exact hB.trans (Nat.mul_le_mul_right p (by dsimp only [c]; omega))

end IntegerMultBounds.MathlibTM2.Cost
