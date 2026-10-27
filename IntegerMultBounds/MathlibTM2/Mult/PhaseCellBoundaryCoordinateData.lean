module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldData
public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec

/-! Structural inverse-fold identity for the retained coordinate page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem unfoldList_foldList {α : Type*} (d : α) (xs : List α) :
    unfoldList (foldList xs) = xs := by
  apply List.ext_getElem (by simp [length_unfoldList,foldList_length])
  intro i hi hj
  have hiX : i < xs.length := by simpa [length_unfoldList,foldList_length] using hi
  have hpos : foldPosN xs.length i < xs.length := by
    unfold foldPosN
    split_ifs <;> omega
  have hindex : foldAtN xs.length (foldPosN xs.length i) = i := by
    unfold foldPosN foldAtN
    split_ifs <;> omega
  have h := getD_unfoldList d (foldList xs) i (by simpa [foldList_length] using hiX)
  rw [foldList_length,getD_foldList d xs _ hpos,hindex,
    List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hiX] at h
  exact h

/-- The same inverse-fold program recovers ascending coordinates from the retained folded page. -/
theorem boundary_unfold_coordinates (s : ℕ) [NeZero s] (B : Finset (ZMod s)) :
    unfoldList ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) =
      (bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)) := by
  rw [← foldList_bOrder,← foldList_map,unfoldList_foldList (0 : GaussianInt)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
