module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedNormalizedWorkspace

/-! The actual zero-replica kernel time inherits the selected shared polynomial. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedNormalizedSetupTime_poly_le (ct cv cB cW : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ B W u target a b V coreWidth k radius : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      B ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      packedKeyNormalizedBatchCost B p q W u l s t a b V (boundaryRecoveryTarget p (target+1))
        (target+1) 2 target coreWidth k radius 0 ≤ C*t^6*p^4 := by
  obtain ⟨C,hcost⟩ := selectedPackedNormalizedWorkspace_zero_poly_le ct cv cB cW
  refine ⟨C,?_⟩
  filter_upwards [hcost] with n hn
  intro h i _ B W u target a b V coreWidth k radius hu ht hab hb hband hV hB hW hhalo
  dsimp only
  exact (packedKeyNormalizedBatchCost_zero_le_workspace ..).trans
    (hn h i B W u target a b V coreWidth k radius hu ht hab hb hband hV hB hW hhalo)

end IntegerMultBounds.MathlibTM2.Cost
