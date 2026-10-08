import IntegerMultBounds.Networks.ProjectionRank

/-! The rational negative-source edge remains correct when sparse support
skips the initial repeated source label. Its actual rank is the first containing
label's dimension, exactly one source dimension above ordinary edge rank. -/

namespace IntegerMultBounds.Networks.ProjectionRank

open Module
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (B : LinearMap.BilinForm K E) (hs : B.IsSymm)

/-- The sum of nested projectors has the larger space as its range when two
is invertible. The explicit preimage compensates by half the smaller projection. -/
theorem nested_sum_range (htwo : (2 : K) ≠ 0) (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    LinearMap.range (project B hs V hv + project B hs U hu) = V := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact V.add_mem (project_mem B hs V hv y) (hUV (project_mem B hs U hu y))
  · intro x hx
    let p := project B hs U hu x
    have hp : p ∈ U := project_mem B hs U hu x
    refine ⟨x - (2 : K)⁻¹ • p, ?_⟩
    simp only [LinearMap.add_apply, map_sub, map_smul,
      project_left B hs V hv hx, project_left B hs V hv (hUV hp),
      project_left B hs U hu hp]
    change x + p - (2 : K)⁻¹ • (p + p) = x
    have ht : (2 : K)⁻¹ • p + (2 : K)⁻¹ • p = p := by
      rw [← add_smul]
      have he : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by field_simp; ring
      rw [he, one_smul]
    rw [smul_add, ht, add_sub_cancel_right]

/-- No hypothesis that the first gate label equals the source line is needed. -/
theorem negative_source_edge_rank (htwo : (2 : K) ≠ 0) (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    finrank K (LinearMap.range (project B hs V hv - (-project B hs U hu))) =
      finrank K V := by
  rw [sub_neg_eq_add, nested_sum_range B hs htwo U V hu hv hUV]

/-- The actual source correction is exactly the source dimension even when
intermediate vertices are absent from a sparse physical history. -/
theorem negative_source_edge_extra (htwo : (2 : K) ≠ 0) (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    finrank K (LinearMap.range (project B hs V hv - (-project B hs U hu))) =
      finrank K (LinearMap.range (project B hs V hv - project B hs U hu)) + finrank K U := by
  rw [negative_source_edge_rank B hs htwo U V hu hv hUV, difference_rank B hs U V hu hv hUV,
    Nat.sub_add_cancel (Submodule.finrank_mono hUV)]

end IntegerMultBounds.Networks.ProjectionRank
