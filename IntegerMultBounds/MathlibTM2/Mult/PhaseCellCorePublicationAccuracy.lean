module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreSubsetPublication

/-! Generated core certificates can be published in their computed class order.
The finite list index is internal to the transfer proof. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem corePublication_errorOn {A s : ℕ} [NeZero s]
    (width L q w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ corePublicationIndices s width L, (rows k).length = L)
    (E : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ corePublicationIndices s width L,
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) x error)
    (k : ℕ) (hk : k ∈ corePublicationIndices s width L) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (scatterRows (L*w) E
        (cstream A w ((corePublicationIndices s width L).map rows).flatten)
        ((corePublicationWindows s width L hw).gaps w))) x error := by
  exact coreSubsetPublication_errorOn width L q w hw (corePublicationIndices s width L)
    (List.Sublist.refl _) rows hrows E hE x error hgood k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
