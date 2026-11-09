module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry

/-! Keep the joint cyclic boundary count in both pieces' precision. The
existing arbitrary-row-count sizing theorem covers this count directly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedCyclicWorkingWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a span : ℕ)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    executionWidth p l (initialSchurTarget p u bits 2) 2 ≤ (1032+8*ct)*p := by
  apply selectedInverseRowWorkingWidth_le ct h i u target _ htarget hband
  simpa only [ZMod.card] using Finset.card_le_univ
    (s := cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a span)

end IntegerMultBounds.MathlibTM2.Cost
