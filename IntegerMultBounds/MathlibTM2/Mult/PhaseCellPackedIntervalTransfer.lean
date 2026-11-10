module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedOutput

/-! Change an interval packet's analytic target without changing its word,
field order, precision or execution. Uniform errors compose once per field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem PackedIntervalOutput.mono {A s p W start rows : ℕ} [NeZero s]
    {targets : List (ZMod s → ℂ)} {error bound : ℝ} {word : List (Fin (A+4))}
    (h : PackedIntervalOutput p W start rows targets error word) (he : error ≤ bound) :
    PackedIntervalOutput p W start rows targets bound word := by
  obtain ⟨Ds,hlen,hword,hgood⟩ := h
  exact ⟨Ds,hlen,hword,hgood.imp (fun _ _ herror i hi => (herror i hi).trans he)⟩

theorem PackedIntervalOutput.transfer {A s p W start rows : ℕ} [NeZero s]
    {xs ys : List (ZMod s → ℂ)} {arithmetic comparison : ℝ} {word : List (Fin (A+4))}
    (h : PackedIntervalOutput p W start rows xs arithmetic word)
    (hxy : List.Forall₂ (fun x y => PhaseCellInterface.ErrorOn
      (haloVertices s start (start+rows)) x y comparison) xs ys) :
    PackedIntervalOutput p W start rows ys (arithmetic+comparison) word := by
  obtain ⟨Ds,hlen,hword,hgood⟩ := h
  refine ⟨Ds,hlen.trans hxy.length_eq,hword,?_⟩
  clear hlen hword
  induction hxy generalizing Ds with
  | nil => cases hgood; exact .nil
  | cons hhead htail ih =>
    cases hgood with
    | cons herror hrest => exact .cons (herror.trans hhead) (ih _ hrest)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
