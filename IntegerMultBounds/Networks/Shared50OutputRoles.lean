import IntegerMultBounds.Networks.Shared50Dirty
import IntegerMultBounds.Networks.Shared50Frames

/-! Physical readout roles have globally distinct target/common-point owners
and the exact source-span label used by the forward frame trace. -/

namespace IntegerMultBounds.Networks.Shared50OutputRoles

open NeighborCounts Shared50Dirty

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50Finite.output pairIndex

/-- Equality of actual partial-output slots identifies both semantic owners. -/
theorem role_eq_iff (T U : Triple 50) (c : {c : Fin 50 // c ∈ T.val})
    (d : {d : Fin 50 // d ∈ U.val}) :
    partialRole T c = partialRole U d ↔ T = U ∧ c.val = d.val := by
  constructor
  · intro he
    have hp := @Shared50Finite.output_injective
      (c.val, pairIndex c.val T c.property) (d.val, pairIndex d.val U d.property) he
    have hc := congrArg Prod.fst hp
    have ht := pairIndex_spec c.val T c.property
    have hu := pairIndex_spec d.val U d.property
    have hh := congrArg (fun p : Fin 50 × Fin 1176 => SharedPointReplay.embedding p.1 p.2) hp
    rw [ht,hu] at hh
    exact ⟨hh,hc⟩
  · rintro ⟨rfl,hc⟩
    have hd : c = d := Subtype.ext hc
    rw [hd]

/-- Exact arithmetic output reference, followed by the actual compiler slot. -/
theorem role_val (T : Triple 50) (c : {c : Fin 50 // c ∈ T.val}) :
    (partialRole T c).val = SharedPointExecution.code.outputSlot
      (SharedPointOutputIndex.index c.val (pairIndex c.val T c.property)) := by
  unfold partialRole Shared50Finite.output
  rfl

/-- The actual forward final label at this finite readout role is the target's
partial-output span. No search or assumed frame attachment remains. -/
theorem final_label (T : Triple 50) (c : {c : Fin 50 // c ∈ T.val}) :
    Shared50Frames.finalLabels (partialRole T c).val = SharedPointMap.outputSpan c.val T := by
  rw [role_val, Shared50Frames.final_label, pairIndex_spec]

theorem final_orthogonal (T : Triple 50) (c : {c : Fin 50 // c ∈ T.val}) :
    Shared50Frames.finalLabels (partialRole T c).val ≤
      (Labels.rational 50).orthogonal (ℚ ∙ (Labels.indicator T.val : Fin 50 → ℚ)) := by
  rw [role_val]
  have hh := Shared50Frames.final_orthogonal c.val (pairIndex c.val T c.property)
  rwa [pairIndex_spec] at hh

end IntegerMultBounds.Networks.Shared50OutputRoles
