module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamRowsCommonWidth

/-! The existing lossless seam widening supplies the same exact core-row
contract as the bulk solver, in the archive's actual replica order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem SeamCropRows.exact_rows_native (p width k : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (h : SeamCropRows p width r J k rows) :
    ExactCoreRows (A := A) p (2*p+13) width k r.inputs.reverse (J r) rows :=
  ⟨h.2.length_eq.symm,h.1,h.2⟩

theorem SeamCropRows.exact_rows (p width W k : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (h : SeamCropRows p width r J k rows) :
    ExactCoreRows (A := A) p W width k r.inputs.reverse (J r) (rows.map (List.map (symZ (2*p+13)))) := by
  obtain ⟨hlen,hgood⟩ := h.commonWidth p width W k hA hW r J rows
  refine ⟨?_,hlen,hgood⟩
  simpa only [List.length_map] using h.2.length_eq.symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
