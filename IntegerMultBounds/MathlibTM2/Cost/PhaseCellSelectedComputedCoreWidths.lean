module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreHeaderWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedCommonWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobRawRecovery

/-! Ordinary canonical job dimensions supply the setup-width profile used by
the complete computed-core fast-time theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedComputedCoreSetup_profile {A : ℕ} (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (r : PackedNormalizedJob A (Sizes.s n i))
    (hp : r.p = Sizes.p n) (ht : r.t = Sizes.t n i)
    (hl : r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (hu : r.u ≤ Sizes.p n) (htarget : r.targetOut ≤ ct*Sizes.p n)
    (hW : r.W = packedHaloCommonWidth r.p r.l (Sizes.s n i) r.u (r.targetOut+1) 2)
    (hB : r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t) :
    let cB := 2*(ct+21)+22
    let cH := 1032+8*ct
    let cZ := cB+cH+ct+20
    r.t = Sizes.t n i ∧ r.Bcore ≤ cZ*Sizes.p n ∧ r.p ≤ cZ*Sizes.p n ∧
      r.u ≤ cZ*Sizes.p n ∧ r.l ≤ cZ*Sizes.p n ∧ r.targetOut ≤ cZ*Sizes.p n ∧
      r.W ≤ cZ*Sizes.p n ∧ PhaseCellBand.width r.p r.u ≤ cZ*Sizes.p n ∧ 2*r.q+8 ≤ cZ*Sizes.p n := by
  dsimp only
  have hband : PhaseCellBand.width (Sizes.p n) r.u ≤ Sizes.s n i := by simpa only [hp] using r.bounds.hband
  have hBc := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  rw [←hp,←hl,←ht,←hB] at hBc
  have hWc := selectedPackedHaloCommonWidth_le ct h i r.u r.targetOut htarget hband
  rw [←hp,←hl,←hW] at hWc
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hlc := (haloInverseRingLog_bounds hp1 (h.good.lt i) (h.quarter_p_le_theta i)).1
  rw [←hl] at hlc
  have hbandc : PhaseCellBand.width r.p r.u ≤ 17*Sizes.p n := by
    have hdiv := Nat.div_le_self (16*r.p) r.u
    have hroot := Nat.sqrt_le_self (16*r.p/r.u)
    unfold PhaseCellBand.width
    omega
  have hn := r.hW
  refine ⟨ht,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals nlinarith only [hBc,hWc,hp,hu,hlc,htarget,hbandc,hn,hp1]

end IntegerMultBounds.MathlibTM2.Cost
