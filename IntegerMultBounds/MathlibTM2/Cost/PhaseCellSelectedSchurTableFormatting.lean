module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSchurTableFormatting
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryWidths
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryFactorPreparation

/-! The shared setup pays its actual boundary-column count times a uniform
computed-column allowance; ordering, collection and cleanup are already priced. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedSchurTableFormatting_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, target ≤ ct*Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      constructedBoundaryTableCostBound p u l s t a b bits ≤
        N*retainedIndexedColumnCost p u l s t a b bits N s+C*t^4 := by
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  refine ⟨3000000*(c+1)^4,?_⟩
  intro n h i _ u target a b htarget hband ha hb
  dsimp only
  obtain ⟨hpt,hN,hq,hw,hV,hW,hB⟩ := hwidths n h i u target a b htarget hband
  let t := Sizes.t n i
  let R := (c+1)*t
  have hst := h.good.lt i
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have htR : t ≤ R := by dsimp only [R]; nlinarith only [Nat.zero_le (c*t)]
  have hR : 1 ≤ R := ht.trans htR
  have hsR : Sizes.s n i ≤ R := hst.le.trans htR
  have hscale : c*Sizes.p n ≤ R := (Nat.mul_le_mul_left c hpt).trans (by
    dsimp only [R,t]; nlinarith only [Nat.zero_le (Sizes.t n i)])
  have hbound := constructedBoundaryTableCostBound_format_le _ _ _ a b _ R hR hsR htR
    (hB.trans hscale) (ha.trans hsR) (hb.trans hsR) (hq.trans hscale) (hw.trans hscale)
    (hV.trans hscale) (hW.trans hscale)
  dsimp only at hbound
  simpa only [R,t,mul_pow,Nat.mul_assoc] using hbound

theorem selectedFamilySetup_columns_le (ct : ℕ) :
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
        N*retainedIndexedColumnCost p u l s t a b bits N s+C*t^6*p^4 := by
  obtain ⟨K,hK⟩ := selectedFamilySetup_table_le ct
  obtain ⟨D,hD⟩ := selectedSchurTableFormatting_le ct
  refine ⟨K+D,?_⟩
  intro n h i _ A u target a b hu htarget hband ha hb
  dsimp only
  have hs := hK n h i A u target a b hu htarget hband ha hb
  have hd := hD n h i u target a b htarget hband ha hb
  dsimp only at hs hd
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hscale := Nat.mul_le_mul_left D (Nat.pow_le_pow_right ht (show 4 ≤ 6 by decide))
  have hscale' := Nat.mul_le_mul_left (D*(Sizes.t n i)^6) (Nat.one_le_pow 4 (Sizes.p n) hp)
  nlinarith only [hs,hd,hscale,hscale']

end IntegerMultBounds.MathlibTM2.Cost
