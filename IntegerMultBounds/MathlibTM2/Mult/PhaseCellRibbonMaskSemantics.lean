module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem ribbonMaskFlag_eq {s t : ℕ} [NeZero s] (boundary : Bool) (hst : s < t)
    (band a b k : ℕ) (hb : b ≤ s) (hband : band ≤ s) :
    haloMaskAt boundary s t band a b ((k+s-band)%s) =
      decide (((k : ZMod s)-(band : ZMod s)) ∈
        (if boundary then haloBoundary s t band a b else haloInterior s t band a b)) := by
  apply Bool.eq_iff_iff.mpr
  rw [haloMaskAt_spec boundary hst band a b _ hb (Nat.mod_lt _ (NeZero.pos s)),decide_eq_true_eq,
    ribbonCoordinate_cast band k hband]

theorem couplingRibbonFlags_eq_map {s t : ℕ} [NeZero s] (boundary : Bool) (hst : s < t)
    (band a b origin N : ℕ) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s) :
    couplingRibbonFlags (s := s) boundary t band a b origin N =
      (List.range (N+2*band)).map (fun j => haloMaskAt boundary s t band a b ((origin+j+s-band)%s)) := by
  apply List.ext_getElem (by simp [couplingRibbonFlags,IntegerMultBounds.NLogN.PhaseCellMatrix.cyclicPaddedLine]; omega)
  intro j hj hj'
  have hjL : j < N+2*band := by simpa using hj'
  simp only [List.getElem_map,List.getElem_range]
  rw [ribbonMaskFlag_eq boundary hst band a b (origin+j) hb hband]
  simp [couplingRibbonFlags,IntegerMultBounds.NLogN.PhaseCellMatrix.cyclicPaddedLine]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
