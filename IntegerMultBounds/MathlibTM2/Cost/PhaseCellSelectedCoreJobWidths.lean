module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreControl
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedCommonWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing

/-! Derived numerical widths discharge the remaining selected core pricing bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main

theorem selectedPackedHaloWorkspaceWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a b : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    packedHaloWorkspaceWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) u (target+1) 2 a b ≤
      (2*(1032+8*ct)+426009)*Sizes.p n := by
  have hw := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hfit := packedHaloCommonWidth_fits (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
    u (target+1) 2 a b
  have hlocal : 2*packedHaloPrecision (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) u (target+1) 2 a b+8 ≤
      (1032+8*ct)*Sizes.p n := hfit.trans hw
  apply selectedWeightWorkspaceWidth_le (1032+8*ct) h i _ _ u hlocal _ hu
  omega

/-- The constructed format determines all three selected width bounds. -/
theorem selectedDerivedCoreWidths_le {A : ℕ} (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (r : PackedNormalizedJob A (Sizes.s n i))
    (hp : r.p = Sizes.p n) (ht : r.t = Sizes.t n i)
    (hl : r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n)
    (hV : r.V = packedHaloWorkspaceWidth r.p r.l (Sizes.s n i) r.t r.u (r.targetOut+1) 2 r.a r.b)
    (hW : r.W = packedHaloCommonWidth r.p r.l (Sizes.s n i) r.u (r.targetOut+1) 2)
    (hB : r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t) :
    r.V ≤ (2*(1032+8*ct)+426009)*Sizes.p n ∧
      r.W ≤ (1032+8*ct)*Sizes.p n ∧ r.Bcore ≤ (2*(ct+21)+22)*Sizes.p n := by
  have hband : PhaseCellBand.width (Sizes.p n) r.u ≤ Sizes.s n i := by
    simpa only [hp] using r.bounds.hband
  constructor
  · rw [hV,hp,hl,ht]
    exact selectedPackedHaloWorkspaceWidth_le ct h i r.u r.targetOut r.a r.b hu htarget hband
  constructor
  · rw [hW,hp,hl]
    exact selectedPackedHaloCommonWidth_le ct h i r.u r.targetOut htarget hband
  · rw [hB,hp,hl,ht]
    exact selectedInverseCallerWordWidth_le ct h i hu htarget hband

/-- Actual canonical job formats require no separately supplied width estimates. -/
theorem selectedDerivedCoreCosts_le_shared_add_linear (ct : ℕ) {T Q : ℕ} {U : Type} :
    ∃ C : ℕ, ∀ n : ℕ, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V = packedHaloWorkspaceWidth r.p r.l (Sizes.s n i) r.t r.u (r.targetOut+1) 2 r.a r.b →
      r.W = packedHaloCommonWidth r.p r.l (Sizes.s n i) r.u (r.targetOut+1) 2 →
      r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t →
      ∀ (input : SupplierInputPlan T) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
        (pushBound : ℕ) (v : HS T Q A U) (S : Stacks T A), plan.Ready r S →
      (coreTimeCost (U := U) producer r.Bcore r ≤ producer.timeCost (U := U) [r]+
        518*r.inputPayload.length+340*r.Fs.length+C*Sizes.t n i^6) ∧
      (coreStock (U := U) producer pushBound r.Bcore r ≤ (pushBound+1)*producer.workspace (U := U) [r]+
        768*r.inputPayload.length+504*r.Fs.length+C*Sizes.t n i^6) := by
  obtain ⟨C,hcost⟩ := selectedCoreCosts_le_shared_add_linear (U := U) ct
    (2*(1032+8*ct)+426009) (1032+8*ct)
  refine ⟨C,?_⟩
  intro n h i _ A r hp ht hl hu htarget hV hW hB input plan producer pushBound v S hready
  have hwidths := selectedDerivedCoreWidths_le ct h i r hp ht hl hu htarget hV hW hB
  exact hcost n h i A r hp ht hl hu htarget hwidths.1 hwidths.2.1 hB input plan producer pushBound v S hready

end IntegerMultBounds.MathlibTM2.Cost
