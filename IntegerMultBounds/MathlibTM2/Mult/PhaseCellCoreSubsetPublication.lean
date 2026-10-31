module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationPreserves

/-! Ordered subsets of a core-length class use the existing publication sweep.
Unselected cores retain complete words even when their lengths agree with the
selected class, as required for separate bulk and seam publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Restrict a window family without changing its ordering or ambient bound. -/
def PublicationWindows.restrict {s L : ℕ} (windows : PublicationWindows s L)
    (origins : List ℕ) (hsub : origins.Sublist windows.origins) : PublicationWindows s L where
  origins := origins
  disjoint := List.Pairwise.sublist hsub windows.disjoint
  fits := fun p hp => windows.fits p (hsub.subset hp)
  count_le := hsub.length_le.trans windows.count_le

def coreSubsetPublicationWindows (s width L : ℕ) (hw : 0 < width)
    (ks : List ℕ) (hks : ks.Sublist (corePublicationIndices s width L)) : PublicationWindows s L :=
  (corePublicationWindows s width L hw).restrict (ks.map (coreStart width)) (hks.map _)

theorem coreSubsetPublication_cost_le (s width L w : ℕ) (hw : 0 < width)
    (ks : List ℕ) (hks : ks.Sublist (corePublicationIndices s width L)) (hw1 : 1 ≤ w) :
    (coreSubsetPublicationWindows s width L hw ks hks).cost w ≤ 35*s*w+6 :=
  PublicationWindows.cost_le _ w hw1

/-- Publishing a selected subset preserves every word of an unselected core.
The two cores may have the same length. -/
theorem coreSubsetPublication_word_preserves {α : Type} {s : ℕ} [NeZero s]
    (width L w : ℕ) (hw : 0 < width) (ks : List ℕ)
    (hks : ks.Sublist (corePublicationIndices s width L))
    (E X : List α) (hE : s*w ≤ E.length) (hX : ks.length*(L*w) ≤ X.length)
    (k : ℕ) (hnot : k ∉ ks) (i : ZMod s)
    (hi : i ∈ ownedCore s width k) :
    ((scatterRows (L*w) E X ((coreSubsetPublicationWindows s width L hw ks hks).gaps w)).drop (i.val*w)).take w =
      (E.drop (i.val*w)).take w := by
  let windows := coreSubsetPublicationWindows s width L hw ks hks
  have hfit : ∀ p ∈ windows.symbolOrigins w, p+L*w ≤ E.length := by
    intro p hp
    obtain ⟨origin,horigin,rfl⟩ := List.mem_map.mp hp
    have hh := Nat.mul_le_mul_right w (windows.fits origin horigin)
    rw [Nat.add_mul] at hh
    exact hh.trans hE
  have hx : (windows.symbolOrigins w).length*(L*w) ≤ X.length := by
    simpa [windows,PublicationWindows.symbolOrigins,coreSubsetPublicationWindows,PublicationWindows.restrict] using hX
  apply scatterRows_slice_off (L*w) (windows.symbolOrigins w) E X
    (windows.symbolOrigins_disjoint w) hfit hx (i.val*w) w
  intro n hn
  have hn' : n < ks.length := by
    simpa [windows,PublicationWindows.symbolOrigins,coreSubsetPublicationWindows,PublicationWindows.restrict] using hn
  let l := ks[n]
  have hl : l ∈ ks := List.getElem_mem hn'
  have hlen := ((mem_corePublicationIndices s width L l).mp (hks.subset hl)).2
  have hne : l ≠ k := by intro he; exact hnot (he ▸ hl)
  have hcross : coreStart width l+L ≤ coreStart width k ∨
      coreStart width k+coreLength s width k ≤ coreStart width l := by
    rcases lt_or_gt_of_ne hne with h | h
    · left; simpa only [hlen] using coreIntervals_ordered s width l k h
    · right; exact coreIntervals_ordered s width k l h
  have hki := (mem_haloVertices _ _ i).mp hi
  simp only [windows,PublicationWindows.symbolOrigins,coreSubsetPublicationWindows,
    PublicationWindows.restrict,List.getElem_map]
  change i.val*w+w ≤ coreStart width l*w ∨ coreStart width l*w+L*w ≤ i.val*w
  rcases hcross with h | h
  · right
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (show coreStart width l+L ≤ i.val by omega)
  · left
    have hh := Nat.mul_le_mul_right w (show i.val+1 ≤ coreStart width l by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh

theorem coreSubsetPublication_errorOn_preserves {A s : ℕ} [NeZero s]
    (width L q w : ℕ) (hw : 0 < width) (ks : List ℕ)
    (hks : ks.Sublist (corePublicationIndices s width L))
    (E X : List (Fin (A+4))) (hE : s*w ≤ E.length) (hX : ks.length*(L*w) ≤ X.length)
    (k : ℕ) (hnot : k ∉ ks)
    (target : ZMod s → ℂ) (error : ℝ)
    (hgood : PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w E) target error) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (scatterRows (L*w) E X ((coreSubsetPublicationWindows s width L hw ks hks).gaps w))) target error := by
  intro i hi
  have he := coreSubsetPublication_word_preserves width L w hw ks hks E X hE hX k hnot i hi
  simpa only [pairedCellRead,he] using hgood i hi

/-- Selected cores receive their certified rows without adding numerical error. -/
theorem coreSubsetPublication_errorOn {A s : ℕ} [NeZero s]
    (width L q w : ℕ) (hw : 0 < width) (ks : List ℕ)
    (hks : ks.Sublist (corePublicationIndices s width L))
    (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ ks, (rows k).length = L)
    (E : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ ks,
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) x error)
    (k : ℕ) (hk : k ∈ ks) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (scatterRows (L*w) E
        (cstream A w ((ks).map rows).flatten)
        ((coreSubsetPublicationWindows s width L hw ks hks).gaps w))) x error := by
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp hk
  let windows := coreSubsetPublicationWindows s width L hw ks hks
  let packedRows := (ks).map rows
  have hcount : packedRows.length = windows.origins.length := by
    simp only [packedRows,windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map]
  have hlength : ∀ row ∈ packedRows, row.length = L := by
    intro row hr
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hr
    subst row
    exact hrows i hi
  have hn' : n < windows.origins.length := by
    simpa only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map] using hn
  have horigin : windows.origins[n] = coreStart width k := by
    simp only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.getElem_map,he]
  have hrow : packedRows[n]'(by rw [hcount]; exact hn') = rows k := by
    simp only [packedRows,List.getElem_map,he]
  have hL := ((mem_corePublicationIndices s width L k).mp (hks.subset hk)).2
  have hcert : PhaseCellInterface.ErrorOn
      (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (packedIntervalRead q w windows.origins[n] (cstream A w packedRows[n])) x error := by
    simpa only [horigin,hrow,ownedCore,hL] using hgood k hk
  have hout := windowPublication_errorOn windows q w packedRows hcount hlength E hE x error n hn' hcert
  simpa only [horigin,ownedCore,hL] using hout


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
