module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobWorkspaceLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedSetupTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreJobWidths

/-! The actual constructed job inherits S3's shared numerical workspace bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedJobSharedWorkspace_poly_le (ct cv cB cW : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V ≤ cv*Sizes.p n → r.Bcore ≤ cB*Sizes.p n → r.W ≤ cW*Sizes.p n →
      r.sharedWorkspace ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨C,hcost⟩ := selectedPackedNormalizedWorkspace_zero_poly_le ct cv cB cW
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
  simpa only [PackedNormalizedJob.sharedWorkspace,hp,ht,hl,hq] using hb

/-- Both shared S3 bills use one uniform constant for the actual derived formats. -/
theorem selectedDerivedCoreSharedCosts_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V = packedHaloWorkspaceWidth r.p r.l (Sizes.s n i) r.t r.u (r.targetOut+1) 2 r.a r.b →
      r.W = packedHaloCommonWidth r.p r.l (Sizes.s n i) r.u (r.targetOut+1) 2 →
      r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t →
      r.setupTime ≤ C*Sizes.t n i^6*Sizes.p n^4 ∧
        r.sharedWorkspace ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  let cv := 2*(1032+8*ct)+426009
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  obtain ⟨Ctime,htime⟩ := selectedPackedJobSetupTime_poly_le ct cv cB cW
  obtain ⟨Cstock,hstock⟩ := selectedPackedJobSharedWorkspace_poly_le ct cv cB cW
  refine ⟨max Ctime Cstock,?_⟩
  filter_upwards [htime,hstock] with n htime hstock
  intro h i _ A r hp ht hl hu htarget hV hW hB
  have hwidths := selectedDerivedCoreWidths_le ct h i r hp ht hl hu htarget hV hW hB
  have hVr : r.V ≤ cv*Sizes.p n := hwidths.1
  have hWr : r.W ≤ cW*Sizes.p n := hwidths.2.1
  have hBr : r.Bcore ≤ cB*Sizes.p n := hwidths.2.2
  constructor
  · exact (htime h i A r hp ht hl hu htarget hVr hBr hWr).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_left Ctime Cstock)))
  · exact (hstock h i A r hp ht hl hu htarget hVr hBr hWr).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right Ctime Cstock)))

end IntegerMultBounds.MathlibTM2.Cost
