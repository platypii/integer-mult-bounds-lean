import IntegerMultBounds.Networks.TensorLabels
import Mathlib.LinearAlgebra.Projection

/-! Orthogonal projection differences on nested nondegenerate subspaces.
This gives the exact edge-rank identity needed by the rational interface; a
complete network must still supply its actual comparable labels. -/

namespace IntegerMultBounds.Networks.ProjectionRank

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)

noncomputable def project (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) : E →ₗ[K] E :=
  U.projection (B.orthogonal U) (B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hu)

theorem project_mem (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) (x : E) :
    project B hs U hu x ∈ U := Submodule.projection_apply_mem _ _

theorem project_left (U : Submodule K E) (hu : (B.restrict U).Nondegenerate)
    {x : E} (hx : x ∈ U) : project B hs U hu x = x :=
  Submodule.projection_apply_of_mem_left _ hx

theorem project_right (U : Submodule K E) (hu : (B.restrict U).Nondegenerate)
    {x : E} (hx : x ∈ B.orthogonal U) : project B hs U hu x = 0 :=
  Submodule.projection_apply_of_mem_right _ hx

theorem sub_project_mem (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) (x : E) :
    x - project B hs U hu x ∈ B.orthogonal U := Submodule.sub_projection_mem _ _

/-- Orthogonal projections commute along a nested pair, in either order. -/
theorem project_nested (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V)
    (x : E) :
    project B hs U hu (project B hs V hv x) = project B hs U hu x ∧
      project B hs V hv (project B hs U hu x) = project B hs U hu x := by
  constructor
  · have hzero := project_right B hs U hu
      ((B.orthogonal_le hUV) (sub_project_mem B hs V hv x))
    rw [map_sub] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · exact project_left B hs V hv (hUV (project_mem B hs U hu x))

/-- The residual is the larger label intersected with the smaller orthogonal
complement, as an actual subspace of the ambient bilinear space. -/
def residual (U V : Submodule K E) : Submodule K E := V ⊓ B.orthogonal U

theorem difference_range (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    LinearMap.range (project B hs V hv - project B hs U hu) = residual B U V := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    change project B hs V hv x - project B hs U hu x ∈ V ⊓ B.orthogonal U
    refine ⟨V.sub_mem (project_mem B hs V hv x) (hUV (project_mem B hs U hu x)), ?_⟩
    rw [← (project_nested B hs U V hu hv hUV x).1]
    exact sub_project_mem B hs U hu (project B hs V hv x)
  · intro z hz
    refine ⟨z, ?_⟩
    change project B hs V hv z - project B hs U hu z = z
    rw [project_left B hs V hv hz.1, project_right B hs U hu hz.2, sub_zero]

include hs in
theorem residual_sup (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hUV : U ≤ V) : U ⊔ residual B U V = V := by
  apply le_antisymm
  · exact sup_le hUV inf_le_left
  · intro x hx
    have hp := project_mem B hs U hu x
    have hr : x - project B hs U hu x ∈ residual B U V :=
      ⟨V.sub_mem hx (hUV hp), sub_project_mem B hs U hu x⟩
    exact Submodule.mem_sup.mpr ⟨_, hp, _, hr, add_sub_cancel _ _⟩

include hs in
theorem residual_disjoint (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) : Disjoint U (residual B U V) :=
  (B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hu).disjoint.mono_right inf_le_right

include hs in
/-- Orthogonal residual dimension equals the actual dimension difference. -/
theorem residual_finrank (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hUV : U ≤ V) :
    finrank K (residual B U V) = finrank K V - finrank K U := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U (residual B U V)
  rw [residual_sup B hs U V hu hUV, (residual_disjoint B hs U V hu).eq_bot,
    finrank_bot, add_zero] at hd
  omega

/-- The rank of the true projection difference, rather than an annotated edge
cost, is precisely the residual dimension. -/
theorem difference_rank (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    finrank K (LinearMap.range (project B hs V hv - project B hs U hu)) =
      finrank K V - finrank K U := by
  rw [difference_range B hs U V hu hv hUV, residual_finrank B hs U V hu hUV]

include hs in
/-- The residual is nondegenerate whenever the containing label is; the
ambient form itself need not be nondegenerate for this local statement. -/
theorem residual_nondegenerate (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    (B.restrict (residual B U V)).Nondegenerate := by
  have hl : (B.restrict (residual B U V)).SeparatingLeft := by
    intro x hx
    have hz : (⟨x.val, x.property.1⟩ : V) = 0 := by
      apply hv.1
      intro y
      have hp := project_mem B hs U hu y
      have hr : (y : E) - project B hs U hu y ∈ residual B U V :=
        ⟨V.sub_mem y.property (hUV hp), sub_project_mem B hs U hu y⟩
      have hleft : B x (project B hs U hu y) = 0 := by
        rw [hs.eq]
        exact x.property.2 _ hp
      have hright : B x ((y : E) - project B hs U hu y) = 0 := hx ⟨_, hr⟩
      change B x y = 0
      have hsum := congrArg (B x) (add_sub_cancel (project B hs U hu y) (y : E))
      rw [map_add, hleft, hright, zero_add] at hsum
      exact hsum.symm
    have hval : (x : E) = 0 := congrArg (fun z : V => (z : E)) hz
    exact Subtype.ext hval
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  change B x y = 0
  rw [hs.eq]
  exact hx y

/-- Orthogonal projection has the actual label as its range. -/
theorem project_rank (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) :
    finrank K (LinearMap.range (project B hs U hu)) = finrank K U := by
  unfold project
  rw [Submodule.range_projection]

include hs in
theorem orthogonal_nondegenerate (hn : B.Nondegenerate) (U : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) : (B.restrict (B.orthogonal U)).Nondegenerate := by
  apply (B.restrict_nondegenerate_iff_isCompl_orthogonal hs.isRefl).mpr
  rw [B.orthogonal_orthogonal hn hs.isRefl U]
  exact (B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hu).symm

/-- Complementary endpoint projectors sum to the identity on every address. -/
theorem complementary_sum (hn : B.Nondegenerate) (U : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) :
    project B hs U hu + project B hs (B.orthogonal U) (orthogonal_nondegenerate B hs hn U hu) =
      LinearMap.id := by
  unfold project
  simp only [B.orthogonal_orthogonal hn hs.isRefl U]
  ext x
  exact Submodule.projection_add_projection_eq_self _ x

/-- The negative source projection is essential: after routing X into Y, the
sink-minus-source map is the full identity, not a partial projection. -/
theorem routed_endpoint (hn : B.Nondegenerate) (U : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) :
    project B hs (B.orthogonal U) (orthogonal_nondegenerate B hs hn U hu) -
      (-project B hs U hu) = LinearMap.id := by
  rw [sub_neg_eq_add, add_comm, complementary_sum B hs hn U hu]

theorem negative_source_rank (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) :
    finrank K (LinearMap.range (-project B hs U hu)) = finrank K U := by
  rw [LinearMap.range_neg, project_rank B hs U hu]

/-- The actual first edge from a negative source projector to the same
positive line costs its dimension: its matrix is twice that projector.
This is the extra source rank in the rational address-shear interface. -/
theorem source_sign_change_rank (htwo : (2 : K) ≠ 0)
    (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) :
    finrank K (LinearMap.range (project B hs U hu - (-project B hs U hu))) = finrank K U := by
  rw [sub_neg_eq_add, ← two_smul K (project B hs U hu), LinearMap.range_smul _ 2 htwo,
    project_rank B hs U hu]

end IntegerMultBounds.Networks.ProjectionRank
