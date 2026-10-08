import IntegerMultBounds.Networks.StageLabels
import IntegerMultBounds.Networks.NeighborResidual

/-! Exact orthogonal residuals of the motif's actual tensor subspaces. -/

namespace IntegerMultBounds.Networks.MotifResiduals

open scoped TensorProduct
open Module TensorSubspace MotifLabels

section General
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- An orthogonal direct-sum decomposition identifies the actual residual. -/
theorem residual_of_split (B : LinearMap.BilinForm K E) (U V W : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hw : W ≤ B.orthogonal U)
    (hsplit : U ⊔ W = V) : ProjectionRank.residual B U V = W := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu', w, hw', hsum⟩ := Submodule.mem_sup.mp (hsplit ▸ hx.1)
    have hu0 : (⟨u, hu'⟩ : U) = 0 := by
      apply hu.2
      intro y
      have hz := hx.2 y y.property
      rw [← hsum, map_add, hw hw' y y.property, add_zero] at hz
      exact hz
    have hz : u = 0 := congrArg Subtype.val hu0
    rw [hz, zero_add] at hsum
    exact hsum ▸ hw'
  · intro w hw'
    exact ⟨hsplit ▸ Submodule.mem_sup_right hw', hw hw'⟩

@[simp] theorem residual_bot (B : LinearMap.BilinForm K E) (V : Submodule K E) :
    ProjectionRank.residual B ⊥ V = V := by
  simp [ProjectionRank.residual]

@[simp] theorem residual_self (B : LinearMap.BilinForm K E) (U : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) : ProjectionRank.residual B U U = ⊥ := by
  exact residual_of_split B U U ⊥ hu bot_le (sup_bot_eq U)
end General

section Tensor
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

theorem residual_tensor_left (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hs : B.IsSymm) (U V : Submodule K E) (L : Submodule K F)
    (hu : (B.restrict U).Nondegenerate) (hl : (C.restrict L).Nondegenerate) (huv : U ≤ V) :
    ProjectionRank.residual (form B C) (space U L) (space V L) =
      space (ProjectionRank.residual B U V) L := by
  apply residual_of_split _ _ _ _ (nondegenerate B C U L hu hl)
  · exact orthogonal_left B C L L inf_le_right
  · rw [← sup_left, ProjectionRank.residual_sup B hs U V hu huv]

theorem residual_tensor_right (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hs : C.IsSymm) (L : Submodule K E) (U V : Submodule K F)
    (hl : (B.restrict L).Nondegenerate) (hu : (C.restrict U).Nondegenerate) (huv : U ≤ V) :
    ProjectionRank.residual (form B C) (space L U) (space L V) =
      space L (ProjectionRank.residual C U V) := by
  apply residual_of_split _ _ _ _ (nondegenerate B C L U hl hu)
  · exact orthogonal_right B C L L inf_le_right
  · rw [← sup_right, ProjectionRank.residual_sup C hs U V hu huv]
end Tensor

namespace Geometry
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (g : MotifLabels.Geometry K E F)

/-- The growing Y input exposes exactly the current-line complement in the base. -/
theorem yIn_common (t : F) (ht : g.current t t ≠ 0) :
    ProjectionRank.residual g.pairing (g.yIn t) g.common =
      space g.base (g.current.orthogonal (K ∙ t)) := by
  change ProjectionRank.residual (form g.earlier g.current) (space g.base (K ∙ t))
    (space g.base ⊤) = _
  rw [residual_tensor_right _ _ g.current_symm _ _ _ g.base_nondegenerate
    (Labels.line_nondegenerate _ _ ht) le_top]
  simp [ProjectionRank.residual]

theorem common_yOut (t : F) :
    ProjectionRank.residual g.pairing g.common (g.yOut t) =
      space g.past (g.current.orthogonal (K ∙ t)) := by
  apply residual_of_split _ _ _ _ g.common_nondegenerate
  · exact orthogonal_left _ _ _ _ (by
      intro x hx y hy
      exact (g.earlier_symm.eq y x).trans (hy x hx))
  · rfl

/-- X's first enlargement has exactly the same residual as Y's first growth. -/
theorem xIn_middle (t : F) (ht : g.current t t ≠ 0) :
    ProjectionRank.residual g.pairing (g.xIn t) (g.xMiddle t) =
      space g.base (g.current.orthogonal (K ∙ t)) := by
  apply residual_of_split _ _ _ _ (g.xIn_nondegenerate t ht)
  · exact orthogonal_right _ _ _ _ le_rfl
  · have hsplit := ProjectionRank.residual_sup g.pairing g.pairing_symm _ _
      (g.yIn_nondegenerate t ht) (g.yIn_le_common t)
    rw [yIn_common g t ht] at hsplit
    change space ⊤ (K ∙ t) ⊔ _ = g.common ⊔ space g.past (K ∙ t)
    rw [← g.base_sup_past, sup_left]
    change (g.yIn t ⊔ space g.past (K ∙ t)) ⊔ _ = _
    rw [sup_right_comm, hsplit]

/-- The second X enlargement exposes the past line times the current complement. -/
theorem middle_full (t : F) (ht : g.current t t ≠ 0) :
    ProjectionRank.residual g.pairing (g.xMiddle t) g.full =
      space g.past (g.current.orthogonal (K ∙ t)) := by
  apply residual_of_split _ _ _ _ (g.xMiddle_nondegenerate t ht)
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 := orthogonal_left g.earlier g.current (g.current.orthogonal (K ∙ t)) ⊤
      (show g.past ≤ g.earlier.orthogonal g.base from fun x hx y hy =>
        (g.earlier_symm.eq y x).trans (hy x hx)) hx a ha
    have h2 := orthogonal_right g.earlier g.current g.past g.past le_rfl hx b hb
    simp only [map_add, LinearMap.add_apply]
    change g.pairing a x = 0 at h1
    change g.pairing b x = 0 at h2
    rw [h1, h2, add_zero]
  · change (g.common ⊔ space g.past (K ∙ t)) ⊔ _ = _
    rw [sup_assoc, ← sup_right,
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal ht).sup_eq_top]
    change space g.base ⊤ ⊔ space g.past ⊤ = _
    rw [← sup_left, g.base_sup_past]
    rfl

/-- Y's last complement restores precisely the omitted past/current tensor line. -/
theorem yOut_full (t : F) (ht : g.current t t ≠ 0) :
    ProjectionRank.residual g.pairing (g.yOut t) g.full = space g.past (K ∙ t) := by
  apply residual_of_split _ _ _ _ (g.yOut_nondegenerate t ht)
  · rw [g.yOut_eq_orthogonal t ht]
    intro x hx y hy
    exact (g.pairing_symm.eq y x).trans (hy x hx)
  · change (g.common ⊔ space g.past (g.current.orthogonal (K ∙ t))) ⊔ _ = _
    rw [sup_assoc, ← sup_right,
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal ht).symm.sup_eq_top]
    change space g.base ⊤ ⊔ space g.past ⊤ = _
    rw [← sup_left, g.base_sup_past]
    rfl
/-- Side scratch first adds a base complement and one orthogonal past line. -/
theorem side_input_middle (tX tY : F) (htY : g.current tY tY ≠ 0) :
    ProjectionRank.residual g.pairing (g.yIn tY) (g.xMiddle tX) =
      space g.base (g.current.orthogonal (K ∙ tY)) ⊔ space g.past (K ∙ tX) := by
  apply residual_of_split _ _ _ _ (g.yIn_nondegenerate tY htY)
  · apply sup_le
    · exact orthogonal_right _ _ _ _ le_rfl
    · exact orthogonal_left _ _ _ _ (by
        intro x hx y hy
        exact (g.earlier_symm.eq y x).trans (hy x hx))
  · rw [← sup_assoc]
    have hh := ProjectionRank.residual_sup g.pairing g.pairing_symm _ _
      (g.yIn_nondegenerate tY htY) (g.yIn_le_common tY)
    rw [yIn_common g tY htY] at hh
    rw [hh]
    rfl

/-- The neighboring side edge removes both physical triple lines from its
current residual, rather than merely recording a dimension difference. -/
theorem side_middle_out (tX tY : F) (htX : g.current tX tX ≠ 0)
    (hneigh : g.current tX tY = 0) :
    ProjectionRank.residual g.pairing (g.xMiddle tX) (g.yOut tY) =
      space g.past (g.current.orthogonal (NeighborResidual.pairSpace tX tY)) := by
  have hc := ProjectionRank.residual_sup g.current g.current_symm (K ∙ tX)
    (g.current.orthogonal (K ∙ tY)) (Labels.line_nondegenerate _ _ htX)
    (g.neighbor_line tX tY hneigh)
  rw [NeighborResidual.side_residual] at hc
  apply residual_of_split _ _ _ _ (g.xMiddle_nondegenerate tX htX)
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 := orthogonal_left g.earlier g.current
      (g.current.orthogonal (NeighborResidual.pairSpace tX tY)) ⊤
      (show g.past ≤ g.earlier.orthogonal g.base from fun x hx y hy =>
        (g.earlier_symm.eq y x).trans (hy x hx)) hx a ha
    have h2 := orthogonal_right g.earlier g.current g.past g.past
      (g.current.orthogonal_le (show K ∙ tX ≤ NeighborResidual.pairSpace tX tY from le_sup_left)) hx b hb
    simp only [map_add, LinearMap.add_apply]
    change g.pairing a x = 0 at h1
    change g.pairing b x = 0 at h2
    rw [h1, h2, add_zero]
  · change (g.common ⊔ space g.past (K ∙ tX)) ⊔ _ = _
    rw [sup_assoc, ← sup_right, hc]
    rfl

section Future
variable {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- Every comparable table residual tensors with the same future line. -/
theorem lift_residual (D : LinearMap.BilinForm K H) (q : H) (hq : D q q ≠ 0)
    (U V : Submodule K (E ⊗[K] F)) (hu : (g.pairing.restrict U).Nondegenerate)
    (huv : U ≤ V) :
    ProjectionRank.residual (g.liftedPairing D)
      (MotifLabels.Geometry.liftLabel q U) (MotifLabels.Geometry.liftLabel q V) =
      MotifLabels.Geometry.liftLabel q (ProjectionRank.residual g.pairing U V) :=
  residual_tensor_left _ _ g.pairing_symm _ _ _ hu
    (Labels.line_nondegenerate D q hq) huv

/-- The scratch sink exposes exactly the future-line complement. -/
theorem scratch_sink_residual (D : LinearMap.BilinForm K H) (hs : D.IsSymm)
    (q : H) (hq : D q q ≠ 0) :
    ProjectionRank.residual (g.liftedPairing D)
      (MotifLabels.Geometry.liftLabel q g.full) ⊤ =
      space (⊤ : Submodule K (E ⊗[K] F)) (D.orthogonal (K ∙ q)) := by
  change ProjectionRank.residual (form g.pairing D) (space g.full (K ∙ q)) ⊤ = _
  rw [g.full_eq_top, ← top_top (K := K) (E := E ⊗[K] F) (F := H),
    residual_tensor_right _ _ hs _ _ _ (top_nondegenerate _ g.pairing_nondegenerate)
      (Labels.line_nondegenerate D q hq) le_top]
  simp [ProjectionRank.residual]
end Future
end Geometry
end IntegerMultBounds.Networks.MotifResiduals
