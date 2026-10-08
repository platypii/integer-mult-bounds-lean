import IntegerMultBounds.Networks.ProjectionRank

/-! Transport actual labels and their orthogonal projections across a linear
isometry. This supports changing tensor coordinates without changing edge ranks. -/

namespace IntegerMultBounds.Networks.LabelTransport

open Module
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y)

def label (U : Submodule K E) : Submodule K F := U.map e.toLinearMap

theorem mem_label (U : Submodule K E) (x : E) : e x ∈ label e U ↔ x ∈ U := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (e.injective hxy) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

include he in
theorem mem_orthogonal (U : Submodule K E) (x : E) :
    e x ∈ C.orthogonal (label e U) ↔ x ∈ B.orthogonal U := by
  constructor
  · intro hx y hy
    rw [← he]
    exact hx (e y) ((mem_label e U y).mpr hy)
  · rintro hx y ⟨y', hy, rfl⟩
    change C (e y') (e x) = 0
    rw [he]
    exact hx y' hy

include he in
theorem nondegenerate (U : Submodule K E) (hu : (B.restrict U).Nondegenerate) :
    (C.restrict (label e U)).Nondegenerate := by
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩⟩ hx
    have hz : (⟨x', hx'⟩ : U) = 0 := hu.1 ⟨x', hx'⟩ (fun y => by
      change B x' y = 0
      rw [← he]
      exact hx ⟨e y, (mem_label e U y).mpr y.property⟩)
    apply Subtype.ext
    have hz' : x' = 0 := congrArg (fun z : U => (z : E)) hz
    simp [hz']
  · rintro ⟨x, ⟨x', hx', rfl⟩⟩ hx
    have hz : (⟨x', hx'⟩ : U) = 0 := hu.2 ⟨x', hx'⟩ (fun y => by
      change B y x' = 0
      rw [← he]
      exact hx ⟨e y, (mem_label e U y).mpr y.property⟩)
    apply Subtype.ext
    have hz' : x' = 0 := congrArg (fun z : U => (z : E)) hz
    simp [hz']

theorem finrank_label (U : Submodule K E) : finrank K (label e U) = finrank K U :=
  (Submodule.equivMapOfInjective e.toLinearMap e.injective U).finrank_eq.symm

include he in
theorem residual (U V : Submodule K E) :
    label e (ProjectionRank.residual B U V) =
      ProjectionRank.residual C (label e U) (label e V) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change e x ∈ label e (ProjectionRank.residual B U V) ↔
    e x ∈ label e V ∧ e x ∈ C.orthogonal (label e U)
  rw [mem_label, mem_label, mem_orthogonal B C e he]
  rfl

include he in
/-- Orthogonal projection is carried to the projection onto the transported
label, so coordinate changes preserve the actual operators. -/
theorem project [FiniteDimensional K E] [FiniteDimensional K F]
    (hs : B.IsSymm) (ht : C.IsSymm) (U : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (x : E) :
    ProjectionRank.project C ht (label e U) (nondegenerate B C e he U hu) (e x) =
      e (ProjectionRank.project B hs U hu x) := by
  have hm := (mem_label e U _).mpr (ProjectionRank.project_mem B hs U hu x)
  have ho := (mem_orthogonal B C e he U _).mpr (ProjectionRank.sub_project_mem B hs U hu x)
  rw [map_sub] at ho
  have hz := ProjectionRank.project_right C ht (label e U) (nondegenerate B C e he U hu) ho
  rw [map_sub, ProjectionRank.project_left C ht _ _ hm] at hz
  exact sub_eq_zero.mp hz

end IntegerMultBounds.Networks.LabelTransport
