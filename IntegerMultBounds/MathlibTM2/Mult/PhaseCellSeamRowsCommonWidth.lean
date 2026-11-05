module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamCrops
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenEncodedPrefix

/-! Carry the actual seam archive's replica order and row guarantees into
common-width publication. Canonicalization does not reorder replicas or rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  ScalarPlacement PhaseCellInterface
variable {A s : ℕ} [NeZero s]

theorem SeamCropRows.commonWidth (p width W k : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (h : SeamCropRows p width r J k rows) :
    let wideRows := rows.map (List.map (symZ (2*p+13)))
    (∀ row ∈ wideRows, row.length = coreLength s width k) ∧
    List.Forall₂ (fun input row =>
      let out := packedIntervalRead p W (coreStart width k) (cstream A W row)
      (∀ i ∈ ownedCore s width k, ‖out i‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))
        (3/(2 : ℝ)^p)) r.inputs.reverse wideRows := by
  dsimp only
  constructor
  · intro row hr
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
    simpa only [List.length_map] using h.1 xs hxs
  · apply List.forall₂_map_right_iff.mpr
    have hall := h.2
    have hlen := h.1
    clear h
    generalize he : r.inputs.reverse = inputs at hall ⊢
    clear he
    induction hall with
    | nil => exact .nil
    | @cons input row inputs rows hgood htail ih =>
      refine .cons ?_ (ih (fun xs hx => hlen xs (by simp [hx])))
      exact widenedCoreRow_accurate hA p (2*p+13) W width k (by omega) hW row
        (hlen row (by simp)) _ _ hgood


/-- The actual seam witness has exactly the volume required by the replica
publication factory and by the counted widening pass. -/
theorem SeamCropRows.commonWidth_volume (p width k : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (h : SeamCropRows p width r J k rows) :
    (rows.flatten.map (symZ (2*p+13))).length = r.inputs.length*coreLength s width k := by
  have hn : rows.length = r.inputs.length := by
    simpa only [List.length_reverse] using h.2.length_eq.symm
  rw [List.length_map,length_flatten_const rows h.1,hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
