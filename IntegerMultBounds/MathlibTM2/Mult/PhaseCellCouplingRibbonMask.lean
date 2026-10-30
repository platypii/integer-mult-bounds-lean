module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSpatialCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedTransferLine

/-! Gather an unmasked ribbon once, then apply halo membership in a local scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def rawCouplingRibbon {s : ℕ} [NeZero s] (band origin N : ℕ)
    (C : ZMod s → GaussianInt) : List GaussianInt :=
  ((cyclicPaddedLine C band).drop origin).take (N+2*band)

/-- Cyclic ribbons retain both wrapped margins, including on a full line. -/
theorem rawCouplingRibbon_length {s : ℕ} [NeZero s] (band origin N : ℕ)
    (C : ZMod s → GaussianInt) (hfit : origin+N ≤ s) :
    (rawCouplingRibbon band origin N C).length = N+2*band := by
  simp only [rawCouplingRibbon,cyclicPaddedLine,List.length_take,List.length_drop,
    List.length_map,List.length_range]
  rw [Nat.min_eq_left (by omega)]

def couplingRibbonFlags {s : ℕ} [NeZero s] (boundary : Bool) (t band a b origin N : ℕ) : List Bool :=
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  ((cyclicPaddedLine (fun j : ZMod s => decide (j ∈ T)) band).drop origin).take (N+2*band)

theorem maskedLine_couplingRibbon {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b origin N : ℕ) (C : ZMod s → GaussianInt) :
    maskedLine (couplingRibbonFlags (s := s) boundary t band a b origin N)
      (rawCouplingRibbon band origin N C) = couplingSourceInterval boundary t band a b origin N C := by
  simp [maskedLine,couplingRibbonFlags,rawCouplingRibbon,couplingSourceInterval,cyclicPaddedLine,
    ← List.map_drop,← List.map_take,List.zipWith_map,List.zipWith_self]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
