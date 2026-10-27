module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary
public import IntegerMultBounds.NLogN.PhaseCellBoundaryOrder

/-! Bound the retained halo boundary by its interval length and original phase cuts. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

def haloBoundaryCountBound (s t band a b : ℕ) : ℕ :=
  min (b-a) (2*band*(t-s+2))

theorem haloBoundary_card_bound {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    (haloBoundary s t band a b).card ≤ haloBoundaryCountBound s t band a b := by
  apply Nat.le_min.mpr
  constructor
  · exact (Finset.card_le_card (Finset.sdiff_subset : haloBoundary s t band a b ⊆ haloVertices s a b)).trans
      (haloVertices_card_le s a b)
  · have hglobal := boundary_card s t hst band (interiorSet s t band) (fun j => mem_interiorSet band j)
    have hsub : haloVertices s a b \ interiorSet s t band ⊆ Finset.univ \ interiorSet s t band := by
      intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j,(Finset.mem_sdiff.mp hj).2⟩
    have hlocal := Finset.card_le_card hsub
    have hhalo := haloBoundary_card_le s t band a b
    nlinarith only [hglobal,hlocal,hhalo]

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
