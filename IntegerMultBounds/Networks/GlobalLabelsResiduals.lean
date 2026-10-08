import IntegerMultBounds.Networks.BinaryMotifResiduals

/-! Extra residual witnesses for sparse physical histories that skip intermediate
motif labels. These are actual tensor vectors, not inferred dimension claims. -/

namespace IntegerMultBounds.Networks.GlobalLabelsResiduals

open scoped TensorProduct
open TensorSubspace MotifLabels BinaryMotifResiduals

variable {h : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (g : Geometry (ZMod 2) E (Fin h → ZMod 2))

/-- A norm-one tensor lies in a residual if its tensor subspace lies there. -/
private theorem residual_unit_of_tensor
    (U V : Submodule (ZMod 2) (E ⊗[ZMod 2] (Fin h → ZMod 2)))
    (W : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hW : ∃ x : W, g.current x x = 1)
    (hle : space g.past W ≤ V) (ho : space g.past W ≤ g.pairing.orthogonal U) :
    Good g.pairing (ProjectionRank.residual g.pairing U V) := by
  obtain ⟨z, hz⟩ := unit_tensor g.earlier g.current (line_unit _ _ g.p_norm) hW
  exact Or.inr ⟨⟨z, ⟨hle z.property, ho z.property⟩⟩, hz⟩

/-- If the copy group is absent, the X input can go straight to full. -/
theorem xIn_full (hcurrent : g.current = Labels.binary h)
    (S : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    Good g.pairing (ProjectionRank.residual g.pairing (g.xIn (Labels.indicator S)) g.full) := by
  have hu : ∃ x : g.current.orthogonal ((ZMod 2) ∙ Labels.indicator S), g.current x x = 1 := by
    rw [hcurrent]
    exact NeighborResidual.triple_complement_unit S hs hh
  apply residual_unit_of_tensor g _ _ _ hu
  · rw [g.full_eq_top]
    exact le_top
  · exact orthogonal_right _ _ _ _ le_rfl

/-- If both central incidences are absent, Y may go directly to its output. -/
theorem yIn_yOut (hcurrent : g.current = Labels.binary h)
    (S : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    Good g.pairing (ProjectionRank.residual g.pairing
      (g.yIn (Labels.indicator S)) (g.yOut (Labels.indicator S))) := by
  have hu : ∃ x : g.current.orthogonal ((ZMod 2) ∙ Labels.indicator S), g.current x x = 1 := by
    rw [hcurrent]
    exact NeighborResidual.triple_complement_unit S hs hh
  apply residual_unit_of_tensor g _ _ _ hu le_sup_right
  exact orthogonal_left _ _ _ _ (by
    intro x hx y hy
    exact (g.earlier_symm.eq y x).trans (hy x hx))

/-- A central wire with no scatter incidence first appears at the full label. -/
theorem bot_full (hcurrent : g.current = Labels.binary h)
    (S : Finset (Fin h)) (hs : S.card = 3) :
    Good g.pairing (ProjectionRank.residual g.pairing ⊥ g.full) := by
  have hu : ∃ x : (⊤ : Submodule (ZMod 2) (Fin h → ZMod 2)), g.current x x = 1 := by
    refine ⟨⟨Labels.indicator S, Submodule.mem_top⟩, ?_⟩
    rw [hcurrent, Labels.binary_self S hs]
  apply residual_unit_of_tensor g _ _ _ hu
  · rw [g.full_eq_top]
    exact le_top
  · simp

section Future
variable [FiniteDimensional (ZMod 2) E]
variable {H : Type*} [AddCommGroup H] [Module (ZMod 2) H] [FiniteDimensional (ZMod 2) H]

/-- The three skipped-label cases survive the actual future-line lift. -/
theorem lifted_skips (hcurrent : g.current = Labels.binary h)
    (D : LinearMap.BilinForm (ZMod 2) H) (q : H) (hq : D q q ≠ 0)
    (S : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    let L := Geometry.liftLabel q
    let B := g.liftedPairing D
    Good B (ProjectionRank.residual B (L (g.xIn (Labels.indicator S))) (L g.full)) ∧
    Good B (ProjectionRank.residual B (L (g.yIn (Labels.indicator S))) (L (g.yOut (Labels.indicator S)))) ∧
    Good B (ProjectionRank.residual B (L ⊥) (L g.full)) := by
  have ht : g.current (Labels.indicator S) (Labels.indicator S) ≠ 0 := by
    rw [hcurrent, Labels.binary_self S hs]
    exact one_ne_zero
  have lift_good (U V : Submodule (ZMod 2) (E ⊗[ZMod 2] (Fin h → ZMod 2)))
      (hU : (g.pairing.restrict U).Nondegenerate) (hle : U ≤ V)
      (hgood : Good g.pairing (ProjectionRank.residual g.pairing U V)) :
      Good (g.liftedPairing D) (ProjectionRank.residual (g.liftedPairing D)
        (Geometry.liftLabel q U) (Geometry.liftLabel q V)) := by
    rw [MotifResiduals.Geometry.lift_residual g D q hq U V hU hle]
    exact good_tensor _ _ hgood (Or.inr (line_unit D q hq))
  exact ⟨lift_good _ _ (g.xIn_nondegenerate _ ht)
      ((g.xIn_le_middle _).trans (g.middle_le_full _)) (xIn_full g hcurrent S hs hh),
    lift_good _ _ (g.yIn_nondegenerate _ ht)
      ((g.yIn_le_common _).trans (g.common_le_yOut _)) (yIn_yOut g hcurrent S hs hh),
    lift_good _ _ (MotifLabels.bot_nondegenerate _) bot_le (bot_full g hcurrent S hs)⟩
end Future
end IntegerMultBounds.Networks.GlobalLabelsResiduals
