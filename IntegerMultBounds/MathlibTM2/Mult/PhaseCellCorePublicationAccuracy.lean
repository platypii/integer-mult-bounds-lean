module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationPreserves

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
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp hk
  let windows := corePublicationWindows s width L hw
  let packedRows := (corePublicationIndices s width L).map rows
  have hcount : packedRows.length = windows.origins.length := by
    simp only [packedRows,windows,corePublicationWindows,List.length_map]
  have hlength : ∀ row ∈ packedRows, row.length = L := by
    intro row hr
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hr
    subst row
    exact hrows i hi
  have hn' : n < windows.origins.length := by
    simpa only [windows,corePublicationWindows,List.length_map] using hn
  have horigin : windows.origins[n] = coreStart width k := by
    simp only [windows,corePublicationWindows,List.getElem_map,he]
  have hrow : packedRows[n]'(by rw [hcount]; exact hn') = rows k := by
    simp only [packedRows,List.getElem_map,he]
  have hL := ((mem_corePublicationIndices s width L k).mp hk).2
  have hcert : PhaseCellInterface.ErrorOn
      (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (packedIntervalRead q w windows.origins[n] (cstream A w packedRows[n])) x error := by
    simpa only [horigin,hrow,ownedCore,hL] using hgood k hk
  have hout := windowPublication_errorOn windows q w packedRows hcount hlength E hE x error n hn' hcert
  simpa only [horigin,ownedCore,hL] using hout

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
