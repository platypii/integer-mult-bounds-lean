module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowPublicationAccuracy

/-! Publishing one core-length class leaves complete words of every other
class intact. This permits sequential sweeps with the same accuracy budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem coreIntervals_ordered (s width k l : ℕ) (hkl : k < l) :
    coreStart width k+coreLength s width k ≤ coreStart width l := by
  have hlen := Nat.min_le_left width (s-coreStart width k)
  have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hkl)
  simp only [Nat.succ_mul] at hm
  dsimp only [coreStart,coreLength] at *
  omega

theorem corePublication_cross_disjoint (s width L M k l : ℕ) (hLM : L ≠ M)
    (hk : k ∈ corePublicationIndices s width L) (hl : l ∈ corePublicationIndices s width M) :
    coreStart width k+L ≤ coreStart width l ∨ coreStart width l+M ≤ coreStart width k := by
  have hk' := (mem_corePublicationIndices s width L k).mp hk
  have hl' := (mem_corePublicationIndices s width M l).mp hl
  have hne : k ≠ l := by intro he; subst l; exact hLM (hk'.2.symm.trans hl'.2)
  rcases lt_or_gt_of_ne hne with h | h
  · left; simpa only [hk'.2] using coreIntervals_ordered s width k l h
  · right; simpa only [hl'.2] using coreIntervals_ordered s width l k h

theorem corePublication_word_preserves {α : Type} {s : ℕ} [NeZero s]
    (width L M w : ℕ) (hw : 0 < width) (hLM : L ≠ M)
    (E X : List α) (hE : s*w ≤ E.length)
    (hX : (corePublicationIndices s width L).length*(L*w) ≤ X.length)
    (k : ℕ) (hk : k ∈ corePublicationIndices s width M) (i : ZMod s)
    (hi : i ∈ ownedCore s width k) :
    ((scatterRows (L*w) E X ((corePublicationWindows s width L hw).gaps w)).drop (i.val*w)).take w =
      (E.drop (i.val*w)).take w := by
  let windows := corePublicationWindows s width L hw
  have hfit : ∀ p ∈ windows.symbolOrigins w, p+L*w ≤ E.length := by
    intro p hp
    change p ∈ windows.origins.map (·*w) at hp
    obtain ⟨origin,horigin,he⟩ := List.mem_map.mp hp
    subst p
    have hh := Nat.mul_le_mul_right w (windows.fits origin horigin)
    rw [Nat.add_mul] at hh
    exact hh.trans hE
  have hx : (windows.symbolOrigins w).length*(L*w) ≤ X.length := by
    simpa [windows,PublicationWindows.symbolOrigins,corePublicationWindows] using hX
  apply scatterRows_slice_off (L*w) (windows.symbolOrigins w) E X
    (windows.symbolOrigins_disjoint w) hfit hx (i.val*w) w
  intro n hn
  have hn' : n < (corePublicationIndices s width L).length := by
    simpa [windows,PublicationWindows.symbolOrigins,corePublicationWindows] using hn
  let l := (corePublicationIndices s width L)[n]
  have hl : l ∈ corePublicationIndices s width L := List.getElem_mem hn'
  have hki := (mem_haloVertices _ _ i).mp hi
  have hklen := ((mem_corePublicationIndices s width M k).mp hk).2
  have hcross := corePublication_cross_disjoint s width L M l k hLM hl hk
  simp only [windows,PublicationWindows.symbolOrigins,corePublicationWindows,List.getElem_map]
  change i.val*w+w ≤ coreStart width l*w ∨ coreStart width l*w+L*w ≤ i.val*w
  rcases hcross with h | h
  · right
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (show coreStart width l+L ≤ i.val by omega)
  · left
    have hh := Nat.mul_le_mul_right w (show i.val+1 ≤ coreStart width l by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh

theorem corePublication_errorOn_preserves {A s : ℕ} [NeZero s]
    (width L M q w : ℕ) (hw : 0 < width) (hLM : L ≠ M)
    (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (corePublicationIndices s width L).length*(L*w) ≤ X.length)
    (k : ℕ) (hk : k ∈ corePublicationIndices s width M)
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w E) x error) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (scatterRows (L*w) E X ((corePublicationWindows s width L hw).gaps w))) x error := by
  intro i hi
  have he := corePublication_word_preserves width L M w hw hLM E X hE hX k hk i hi
  simpa only [pairedCellRead,he] using hgood i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
