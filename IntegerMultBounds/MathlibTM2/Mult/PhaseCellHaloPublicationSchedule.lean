module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterSchedule

/-! The clipped origins' advances yield the exact ambient publication gaps. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloPublicationGaps (s t band a b L w : ℕ) :
    publicationGaps (L*w) (originAdvances w 0 (haloOrigins s t band a b L)) =
      haloScatterGaps s t band a b L w := by
  rw [originAdvances_symbols]
  simpa only [Nat.zero_mul,haloScatterGaps,haloSymbolOrigins] using
    (windowGaps_publicationGaps (L*w) ((haloOrigins s t band a b L).map (·*w))).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
