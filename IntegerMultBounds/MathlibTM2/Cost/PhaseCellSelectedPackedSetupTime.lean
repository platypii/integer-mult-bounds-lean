module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedNormalizedWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobTimeLedger

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

/-- Apply the selected setup bill to a constructed job. Its packet geometry and
precision are derived; the remaining premises are selected parameter bounds. -/
theorem selectedPackedJobSetupTime_poly_le (ct cv cB cW : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V ≤ cv*Sizes.p n → r.Bcore ≤ cB*Sizes.p n → r.W ≤ cW*Sizes.p n →
      r.setupTime ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨C,hcost⟩ := selectedPackedNormalizedSetupTime_poly_le ct cv cB cW
  refine ⟨C,?_⟩
  filter_upwards [hcost] with n hn
  intro h i _ A r hp ht hl hu htarget hV hB hW
  have hq : r.q = executionPrecision (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (initialSchurTarget (Sizes.p n) r.u
        (boundaryTableBits (Sizes.p n) (boundaryRecoveryTarget (Sizes.p n) (r.targetOut+1)) 2
          (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) r.u) r.a r.b).card) 2) 2 := by
    rw [r.precision_eq,hp,ht,hl,inverseExecutionExponent_eq]
    rfl
  have hb := hn h i r.Bcore r.W r.u r.targetOut r.a r.b r.V r.coreWidth r.k r.radius
    hu htarget r.bounds.hab r.bounds.hbs
    (by simpa only [hp] using r.bounds.hband) hV hB hW (by rw [r.haloLength])
  simpa only [PackedNormalizedJob.setupTime,hp,ht,hl,hq] using hb

end IntegerMultBounds.MathlibTM2.Cost
