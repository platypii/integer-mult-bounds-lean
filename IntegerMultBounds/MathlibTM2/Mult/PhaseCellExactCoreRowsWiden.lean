module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenEncodedPrefix

/-! Lossless width conversion for the shared bulk/seam row language. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.LayerMachine
variable {A s : ℕ} [NeZero s]

theorem ExactCoreRows.widen {p w W width k : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    {rows : List (List GaussianInt)} (h : ExactCoreRows (A := A) p w width k Fs J rows)
    (hA : 4 ≤ A) (hw : 1 ≤ w) (hW : w ≤ W) :
    ExactCoreRows (A := A) p W width k Fs J (rows.map (List.map (symZ w))) := by
  refine ⟨by simpa only [List.length_map] using h.1,?_,?_⟩
  · intro row hr
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
    simpa only [List.length_map] using h.2.1 xs hxs
  · apply List.forall₂_map_right_iff.mpr
    have hlen := h.2.1
    have hall := h.2.2
    clear h
    induction hall with
    | nil => exact .nil
    | @cons F row Fs rows hgood htail ih =>
      refine .cons ?_ (ih (fun xs hx => hlen xs (by simp [hx])))
      exact widenedCoreRow_accurate hA p w W width k hw hW row
        (hlen row (by simp)) _ _ hgood

theorem exactCoreRows_widen_batches {p w W width : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    {ks : List ℕ} {batches : List (List (List GaussianInt))}
    (h : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p w width k Fs J rows) ks batches)
    (hA : 4 ≤ A) (hw : 1 ≤ w) (hW : w ≤ W) :
    List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W width k Fs J rows)
      ks (batches.map (List.map (List.map (symZ w)))) := by
  apply List.forall₂_map_right_iff.mpr
  exact h.imp (by intro k rows hr; exact hr.widen hA hw hW)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
