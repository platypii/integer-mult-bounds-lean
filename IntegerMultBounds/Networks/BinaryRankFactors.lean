import IntegerMultBounds.Networks.BinaryColumns
import IntegerMultBounds.Networks.ProjectionTrace
import IntegerMultBounds.Networks.LabelTransport
import IntegerMultBounds.Networks.TensorCoordinates
import IntegerMultBounds.Networks.BinaryMotifResiduals

/-! Factor counts derived from genuine projection ranks. Both orientations of
an actual binary frame edge are handled; no rank is assigned to an unrelated
replacement operation. The residual-unit premise is explicit here. -/

namespace IntegerMultBounds.Networks.BinaryRankFactors

open Module BinaryWalsh BinaryPhase BinaryColumns

variable {h k : ℕ}

noncomputable def labelFrame (hs : (Labels.binary h).IsSymm)
    (U : Submodule (ZMod 2) (Address h)) :=
  frame (fun x => weightPhase (ProjectionTrace.projector (Labels.binary h) hs U x))

noncomputable def edgeOperator (hs : (Labels.binary h).IsSymm) (k : ℕ)
    (U V : Submodule (ZMod 2) (Address h)) : Operator h k :=
  tensorColumns k (labelFrame hs V).toLinearMap *
    tensorColumns k (labelFrame hs U).symm.toLinearMap

/-- Either direction of a nested binary edge has exactly its true projection
rank many vector factors, with only the allowed forward/inverse kernel signs.
The same kernel list works for every number of columns. -/
theorem exists_uniform_rank_factors (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate)
    (hedge : (U ≤ V ∧ (ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
        ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1)) ∨
      (V ≤ U ∧ (ProjectionRank.residual (Labels.binary h) V U = ⊥ ∨
        ∃ v : ProjectionRank.residual (Labels.binary h) V U, Labels.binary h v v = 1))) :
    ∃ gs : List (ZMod 4 × Address h),
      gs.length = ProjectionTrace.edgeRank (Labels.binary h) hs U V ∧
      (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
      ∀ k, edgeOperator hs k U V = (gs.map (vectorFactor k)).prod := by
  rcases hedge with ⟨hle, hg⟩ | ⟨hle, hg⟩
  · obtain ⟨gs, hlen, hsign, hf, _⟩ := exists_edge_kernels hs U V hu hv hle hg
    refine ⟨gs, ?_, hsign, ?_⟩
    · rw [ProjectionTrace.edgeRank_eq _ hs U V hu hv (Or.inl hle),
        Nat.sub_eq_zero_of_le (Submodule.finrank_mono hle), add_zero]
      exact hlen
    · intro k
      unfold edgeOperator labelFrame
      rw [ProjectionTrace.projector_eq _ hs U hu, ProjectionTrace.projector_eq _ hs V hv]
      exact edge_factor_product _ _ gs hf
  · obtain ⟨gs, hlen, hsign, _, hr⟩ := exists_edge_kernels hs V U hv hu hle hg
    refine ⟨negateKernels gs, ?_, ?_, ?_⟩
    · rw [ProjectionTrace.edgeRank_eq _ hs U V hu hv (Or.inr hle),
        Nat.sub_eq_zero_of_le (Submodule.finrank_mono hle), zero_add]
      simpa only [negateKernels, List.length_map] using hlen
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rcases hsign g' hg' with hp | hn
      · exact Or.inr (congrArg Neg.neg hp)
      · left
        simp only [hn, neg_neg]
    · intro k
      unfold edgeOperator labelFrame
      rw [ProjectionTrace.projector_eq _ hs U hu, ProjectionTrace.projector_eq _ hs V hv]
      exact edge_factor_product _ _ (negateKernels gs) hr

/-- Either direction of a nested binary edge has exactly its true projection
rank many vector factors, with only the allowed forward/inverse kernel signs. -/
theorem exists_rank_factors (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Address h))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate)
    (hedge : (U ≤ V ∧ (ProjectionRank.residual (Labels.binary h) U V = ⊥ ∨
        ∃ v : ProjectionRank.residual (Labels.binary h) U V, Labels.binary h v v = 1)) ∨
      (V ≤ U ∧ (ProjectionRank.residual (Labels.binary h) V U = ⊥ ∨
        ∃ v : ProjectionRank.residual (Labels.binary h) V U, Labels.binary h v v = 1))) :
    ∃ gs : List (ZMod 4 × Address h),
      gs.length = ProjectionTrace.edgeRank (Labels.binary h) hs U V ∧
      (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
      edgeOperator hs k U V = (gs.map (vectorFactor k)).prod := by
  obtain ⟨gs, hlen, hsign, hop⟩ := exists_uniform_rank_factors hs U V hu hv hedge
  exact ⟨gs, hlen, hsign, hop k⟩

section Transport
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

/-- An isometric coordinate change preserves both the actual edge rank and
its realization by binary vector factors. -/
theorem exists_uniform_transport_factors (B : LinearMap.BilinForm (ZMod 2) E) (hs : B.IsSymm)
    (hc : (Labels.binary h).IsSymm) (e : E ≃ₗ[ZMod 2] Address h)
    (he : ∀ x y, Labels.binary h (e x) (e y) = B x y)
    (U V : Submodule (ZMod 2) E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate)
    (hedge : (U ≤ V ∧ BinaryMotifResiduals.Good B (ProjectionRank.residual B U V)) ∨
      (V ≤ U ∧ BinaryMotifResiduals.Good B (ProjectionRank.residual B V U))) :
    ∃ gs : List (ZMod 4 × Address h),
      gs.length = ProjectionTrace.edgeRank B hs U V ∧
      (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
      ∀ k, edgeOperator hc k (LabelTransport.label e U) (LabelTransport.label e V) =
        (gs.map (vectorFactor k)).prod := by
  have hu' := LabelTransport.nondegenerate B (Labels.binary h) e he U hu
  have hv' := LabelTransport.nondegenerate B (Labels.binary h) e he V hv
  have hUV : U ≤ V ∨ V ≤ U := hedge.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hcUV : LabelTransport.label e U ≤ LabelTransport.label e V ∨
      LabelTransport.label e V ≤ LabelTransport.label e U :=
    hUV.elim (fun h => Or.inl (Submodule.map_mono h)) (fun h => Or.inr (Submodule.map_mono h))
  have hgood :
      (LabelTransport.label e U ≤ LabelTransport.label e V ∧
        BinaryMotifResiduals.Good (Labels.binary h) (ProjectionRank.residual (Labels.binary h)
          (LabelTransport.label e U) (LabelTransport.label e V))) ∨
      (LabelTransport.label e V ≤ LabelTransport.label e U ∧
        BinaryMotifResiduals.Good (Labels.binary h) (ProjectionRank.residual (Labels.binary h)
          (LabelTransport.label e V) (LabelTransport.label e U))) := by
    rcases hedge with ⟨hle, hg⟩ | ⟨hle, hg⟩
    · exact Or.inl ⟨Submodule.map_mono hle,
        BinaryMotifResiduals.residual_good_transport B _ e he U V hg⟩
    · exact Or.inr ⟨Submodule.map_mono hle,
        BinaryMotifResiduals.residual_good_transport B _ e he V U hg⟩
  obtain ⟨gs, hlen, hsign, hop⟩ := exists_uniform_rank_factors hc
    (LabelTransport.label e U) (LabelTransport.label e V) hu' hv' hgood
  refine ⟨gs, ?_, hsign, hop⟩
  rw [ProjectionTrace.edgeRank_eq _ hc _ _ hu' hv' hcUV,
    LabelTransport.finrank_label, LabelTransport.finrank_label] at hlen
  rw [ProjectionTrace.edgeRank_eq B hs U V hu hv hUV]
  exact hlen

/-- Realize every edge in a supplied ordered trace, retaining its exact
operator and signs, with aggregate factor count equal to the actual rank sum. -/
theorem exists_uniform_list_transport_factors (B : LinearMap.BilinForm (ZMod 2) E) (hs : B.IsSymm)
    (hc : (Labels.binary h).IsSymm) (e : E ≃ₗ[ZMod 2] Address h)
    (he : ∀ x y, Labels.binary h (e x) (e y) = B x y)
    (edges : List (Submodule (ZMod 2) E × Submodule (ZMod 2) E))
    (hnd : ∀ p ∈ edges, (B.restrict p.1).Nondegenerate ∧ (B.restrict p.2).Nondegenerate)
    (hgood : ∀ p ∈ edges,
      (p.1 ≤ p.2 ∧ BinaryMotifResiduals.Good B (ProjectionRank.residual B p.1 p.2)) ∨
      (p.2 ≤ p.1 ∧ BinaryMotifResiduals.Good B (ProjectionRank.residual B p.2 p.1))) :
    ∃ factors : List (List (ZMod 4 × Address h)),
      List.Forall₂ (fun p gs =>
        (∀ g ∈ gs, g.1 = 1 ∨ g.1 = -1) ∧
        ∀ k, edgeOperator hc k (LabelTransport.label e p.1) (LabelTransport.label e p.2) =
          (gs.map (vectorFactor k)).prod) edges factors ∧
      (factors.map List.length).sum =
        (edges.map (fun p => ProjectionTrace.edgeRank B hs p.1 p.2)).sum := by
  induction edges with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons p ps ih =>
    obtain ⟨hu, hv⟩ := hnd p (by simp)
    obtain ⟨gs, hlen, hsign, hop⟩ := exists_uniform_transport_factors B hs hc e he p.1 p.2 hu hv
      (hgood p (by simp))
    obtain ⟨rest, hrest, hsum⟩ := ih (fun q hq => hnd q (by simp [hq]))
      (fun q hq => hgood q (by simp [hq]))
    exact ⟨gs :: rest, .cons ⟨hsign, hop⟩ hrest, by simp only [List.map_cons, List.sum_cons, hlen, hsum]⟩

end Transport
end IntegerMultBounds.Networks.BinaryRankFactors
