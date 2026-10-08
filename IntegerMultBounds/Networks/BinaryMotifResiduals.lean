import IntegerMultBounds.Networks.MotifResiduals
import IntegerMultBounds.Networks.LabelTransport

/-! Concrete characteristic-two nonalternation witnesses for all motif edges.
Zero residuals are distinguished from nonzero residuals with norm-one vectors. -/

namespace IntegerMultBounds.Networks.BinaryMotifResiduals

open scoped TensorProduct
open Module TensorSubspace MotifLabels

section Witnesses
variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]

/-- Exactly the zero-or-norm-one alternative needed for orthonormal residuals. -/
def Good (B : LinearMap.BilinForm (ZMod 2) E) (U : Submodule (ZMod 2) E) : Prop :=
  U = ⊥ ∨ ∃ x : U, B x x = 1

theorem good_bot (B : LinearMap.BilinForm (ZMod 2) E) : Good B ⊥ := Or.inl rfl

theorem unit_tensor (B : LinearMap.BilinForm (ZMod 2) E) (C : LinearMap.BilinForm (ZMod 2) F)
    {U : Submodule (ZMod 2) E} {V : Submodule (ZMod 2) F}
    (hu : ∃ x : U, B x x = 1) (hv : ∃ y : V, C y y = 1) :
    ∃ z : space U V, form B C z z = 1 := by
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  refine ⟨⟨(x : E) ⊗ₜ[ZMod 2] (y : F), tmul_mem _ _ x.property y.property⟩, ?_⟩
  simp only [LinearMap.BilinForm.tensorDistrib_tmul, hx, hy, smul_eq_mul, mul_one]

theorem good_tensor (B : LinearMap.BilinForm (ZMod 2) E) (C : LinearMap.BilinForm (ZMod 2) F)
    {U : Submodule (ZMod 2) E} {V : Submodule (ZMod 2) F}
    (hu : Good B U) (hv : Good C V) : Good (form B C) (space U V) := by
  rcases hu with rfl | hu
  · exact Or.inl (StageLabels.space_bot_left V)
  rcases hv with rfl | hv
  · left
    apply le_antisymm _ bot_le
    apply StageLabels.space_le
    intro u _ v hv
    have hz : v = 0 := by simpa using hv
    simp [hz]
  · exact Or.inr (unit_tensor B C hu hv)

theorem good_sup_of_right_unit (B : LinearMap.BilinForm (ZMod 2) E)
    (U V : Submodule (ZMod 2) E) (hv : ∃ x : V, B x x = 1) : Good B (U ⊔ V) := by
  obtain ⟨x, hx⟩ := hv
  exact Or.inr ⟨⟨x, Submodule.mem_sup_right x.property⟩, hx⟩

theorem binary_nonzero_eq_one (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl

theorem line_unit (B : LinearMap.BilinForm (ZMod 2) E) (x : E) (hx : B x x ≠ 0) :
    ∃ y : (ZMod 2) ∙ x, B y y = 1 :=
  ⟨⟨x, Submodule.mem_span_singleton_self x⟩, binary_nonzero_eq_one _ hx⟩

/-- Actual norm-one witnesses survive the proved stage and binary-coordinate
isometries, so changing the ambient representation creates no new assumption. -/
theorem good_transport (B : LinearMap.BilinForm (ZMod 2) E)
    (C : LinearMap.BilinForm (ZMod 2) F) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ x y, C (e x) (e y) = B x y) (U : Submodule (ZMod 2) E)
    (hu : Good B U) : Good C (LabelTransport.label e U) := by
  rcases hu with rfl | ⟨x, hx⟩
  · left
    exact Submodule.map_bot _
  · right
    exact ⟨⟨e x, (LabelTransport.mem_label e U x).mpr x.property⟩, (he x x).trans hx⟩

theorem residual_good_transport (B : LinearMap.BilinForm (ZMod 2) E)
    (C : LinearMap.BilinForm (ZMod 2) F) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ x y, C (e x) (e y) = B x y) (U V : Submodule (ZMod 2) E)
    (hu : Good B (ProjectionRank.residual B U V)) :
    Good C (ProjectionRank.residual C (LabelTransport.label e U) (LabelTransport.label e V)) := by
  rw [← LabelTransport.residual B C e he U V]
  exact good_transport B C e he _ hu

end Witnesses

section Table
variable {h : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (g : MotifLabels.Geometry (ZMod 2) E (Fin h → ZMod 2))

/-- The distinct directed label comparisons used by the X, Y, side, and central
wire paths. The central return uses the same comparison with reverse phase. -/
def tableEdges (tX tY : Fin h → ZMod 2) :
    List (Submodule (ZMod 2) (E ⊗[ZMod 2] (Fin h → ZMod 2)) ×
      Submodule (ZMod 2) (E ⊗[ZMod 2] (Fin h → ZMod 2))) :=
  [(g.xIn tX, g.xMiddle tX), (g.xMiddle tX, g.full),
   (g.yIn tY, g.common), (g.common, g.yOut tY),
   (⊥, g.yIn tY), (g.yIn tY, g.xMiddle tX),
   (g.xMiddle tX, g.yOut tY), (g.yOut tY, g.full),
   (⊥, g.common), (g.common, g.full),
   (g.full, g.full), (g.yIn tY, g.yIn tY), (g.common, g.common)]

/-- Every listed comparison is genuinely nested with a nondegenerate source. -/
theorem tableEdges_valid (tX tY : Fin h → ZMod 2)
    (hx : g.current tX tX ≠ 0) (hy : g.current tY tY ≠ 0)
    (hxy : g.current tX tY = 0) :
    ∀ e ∈ tableEdges g tX tY, e.1 ≤ e.2 ∧ (g.pairing.restrict e.1).Nondegenerate := by
  intro e he
  simp only [tableEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨g.xIn_le_middle tX, g.xIn_nondegenerate tX hx⟩
    | exact ⟨g.middle_le_full tX, g.xMiddle_nondegenerate tX hx⟩
    | exact ⟨g.yIn_le_common tY, g.yIn_nondegenerate tY hy⟩
    | exact ⟨g.common_le_yOut tY, g.common_nondegenerate⟩
    | exact ⟨bot_le, MotifLabels.bot_nondegenerate _⟩
    | exact ⟨(g.yIn_le_common tY).trans le_sup_left, g.yIn_nondegenerate tY hy⟩
    | exact ⟨g.side_middle_le_out tX tY hxy, g.xMiddle_nondegenerate tX hx⟩
    | exact ⟨g.yOut_le_full tY, g.yOut_nondegenerate tY hy⟩
    | exact ⟨g.common_le_full, g.common_nondegenerate⟩
    | exact ⟨le_rfl, g.full_nondegenerate⟩
    | exact ⟨le_rfl, g.yIn_nondegenerate tY hy⟩
    | exact ⟨le_rfl, g.common_nondegenerate⟩

/-- Triple supports supply every current-factor unit; only the earlier base
alternative remains abstract here and is discharged by the stage theorems. -/
theorem tableEdges_good (hcurrent : g.current = Labels.binary h)
    (hbase : Good g.earlier g.base) (S T : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    ∀ e ∈ tableEdges g (Labels.indicator S) (Labels.indicator T),
      Good g.pairing (ProjectionRank.residual g.pairing e.1 e.2) := by
  let x := Labels.indicator (R := ZMod 2) S
  let y := Labels.indicator (R := ZMod 2) T
  have hx : g.current x x ≠ 0 := by rw [hcurrent, Labels.binary_self S hs]; exact one_ne_zero
  have hy : g.current y y ≠ 0 := by rw [hcurrent, Labels.binary_self T ht]; exact one_ne_zero
  have hxy : g.current x y = 0 := by rw [hcurrent]; exact Labels.binary_neighbors S T hneigh
  have hp : ∃ v : g.past, g.earlier v v = 1 := line_unit _ _ g.p_norm
  have hcx : ∃ v : g.current.orthogonal ((ZMod 2) ∙ x), g.current v v = 1 := by
    rw [hcurrent]
    exact NeighborResidual.triple_complement_unit S hs (by omega)
  have hcy : ∃ v : g.current.orthogonal ((ZMod 2) ∙ y), g.current v v = 1 := by
    rw [hcurrent]
    exact NeighborResidual.triple_complement_unit T ht (by omega)
  have hcp : ∃ v : g.current.orthogonal (NeighborResidual.pairSpace x y), g.current v v = 1 := by
    rw [hcurrent]
    exact NeighborResidual.pair_complement_unit S T hs ht hh
  have hfull : ∃ v : (⊤ : Submodule (ZMod 2) (Fin h → ZMod 2)), g.current v v = 1 :=
    ⟨⟨x, Submodule.mem_top⟩, binary_nonzero_eq_one _ hx⟩
  intro e he
  change e ∈ tableEdges g x y at he
  simp only [tableEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [MotifResiduals.Geometry.xIn_middle g x hx]
    exact good_tensor _ _ hbase (Or.inr hcx)
  · rw [MotifResiduals.Geometry.middle_full g x hx]
    exact Or.inr (unit_tensor _ _ hp hcx)
  · rw [MotifResiduals.Geometry.yIn_common g y hy]
    exact good_tensor _ _ hbase (Or.inr hcy)
  · rw [MotifResiduals.Geometry.common_yOut g y]
    exact Or.inr (unit_tensor _ _ hp hcy)
  · rw [MotifResiduals.residual_bot]
    exact good_tensor _ _ hbase (Or.inr (line_unit _ y hy))
  · rw [MotifResiduals.Geometry.side_input_middle g x y hy]
    exact good_sup_of_right_unit _ _ _ (unit_tensor _ _ hp (line_unit _ x hx))
  · rw [MotifResiduals.Geometry.side_middle_out g x y hx hxy]
    exact Or.inr (unit_tensor _ _ hp hcp)
  · rw [MotifResiduals.Geometry.yOut_full g y hy]
    exact Or.inr (unit_tensor _ _ hp (line_unit _ y hy))
  · rw [MotifResiduals.residual_bot]
    exact good_tensor _ _ hbase (Or.inr hfull)
  · rw [g.central_residual_eq]
    exact Or.inr (unit_tensor _ _ hp hfull)
  · rw [MotifResiduals.residual_self _ _ g.full_nondegenerate]
    exact good_bot _
  · rw [MotifResiduals.residual_self _ _ (g.yIn_nondegenerate y hy)]
    exact good_bot _
  · rw [MotifResiduals.residual_self _ _ g.common_nondegenerate]
    exact good_bot _

section Future
variable {H : Type*} [AddCommGroup H] [Module (ZMod 2) H] [FiniteDimensional (ZMod 2) H]

/-- All local wire residuals after restoring the future line, including the
scratch sink's final enlargement to the complete ambient space. -/
def AllResiduals (D : LinearMap.BilinForm (ZMod 2) H) (q : H)
    (tX tY : Fin h → ZMod 2) : Prop :=
  (∀ e ∈ tableEdges g tX tY,
    Good (g.liftedPairing D) (ProjectionRank.residual (g.liftedPairing D)
      (MotifLabels.Geometry.liftLabel q e.1) (MotifLabels.Geometry.liftLabel q e.2))) ∧
  Good (g.liftedPairing D) (ProjectionRank.residual (g.liftedPairing D)
    (MotifLabels.Geometry.liftLabel q g.full) ⊤)

theorem allResiduals_of_witnesses (hcurrent : g.current = Labels.binary h)
    (hbase : Good g.earlier g.base)
    (D : LinearMap.BilinForm (ZMod 2) H) (hD : D.IsSymm) (q : H) (hq : D q q ≠ 0)
    (hfuture : Good D (D.orthogonal ((ZMod 2) ∙ q)))
    (S T : Finset (Fin h)) (hs : S.card = 3) (ht : T.card = 3)
    (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    AllResiduals g D q (Labels.indicator S) (Labels.indicator T) := by
  have hx : g.current (Labels.indicator S) (Labels.indicator S) ≠ 0 := by
    rw [hcurrent, Labels.binary_self S hs]; exact one_ne_zero
  have hy : g.current (Labels.indicator T) (Labels.indicator T) ≠ 0 := by
    rw [hcurrent, Labels.binary_self T ht]; exact one_ne_zero
  have hxy : g.current (Labels.indicator S) (Labels.indicator T) = 0 := by
    rw [hcurrent]; exact Labels.binary_neighbors S T hneigh
  constructor
  · intro e he
    obtain ⟨hle, hnd⟩ := tableEdges_valid g _ _ hx hy hxy e he
    rw [MotifResiduals.Geometry.lift_residual g D q hq _ _ hnd hle]
    exact good_tensor _ _ (tableEdges_good g hcurrent hbase S T hs ht hneigh hh e he)
      (Or.inr (line_unit D q hq))
  · rw [MotifResiduals.Geometry.scratch_sink_residual g D hD q hq]
    apply good_tensor _ _ _ hfuture
    right
    refine ⟨⟨g.p ⊗ₜ[ZMod 2] Labels.indicator S, Submodule.mem_top⟩, ?_⟩
    change form g.earlier g.current _ _ = 1
    simp only [LinearMap.BilinForm.tensorDistrib_tmul,
      binary_nonzero_eq_one _ g.p_norm, binary_nonzero_eq_one _ hx, smul_eq_mul, mul_one]
end Future
end Table

section Stages
open Labels StageLabels
variable {h : ℕ}

private theorem binary_symm : (binary h).IsSymm := ⟨form_symm 0⟩
private theorem triple_nonzero (S : Finset (Fin h)) (hs : S.card = 3) :
    binary h (indicator S) (indicator S) ≠ 0 := by
  rw [binary_self S hs]
  exact one_ne_zero

/-- Stage one has zero earlier base, and the actual future two-triple line
complement contains a coordinate tensor of norm one. No residual witness is assumed. -/
theorem first_allResiduals (A B S T : Finset (Fin h))
    (ha : A.card = 3) (hb : B.card = 3) (hs : S.card = 3) (ht : T.card = 3)
    (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    AllResiduals (firstGeometry (binary h) binary_symm binary_nondegenerate)
      (form (binary h) (binary h)) (indicator A ⊗ₜ[ZMod 2] indicator B)
      (indicator S) (indicator T) := by
  apply allResiduals_of_witnesses _ rfl
  · left
    change (unitForm : LinearMap.BilinForm (ZMod 2) (ZMod 2)).orthogonal
      ((ZMod 2) ∙ (1 : ZMod 2)) = ⊥
    rw [scalar_line_one, unit_orthogonal_top]
  · exact LinearMap.BilinForm.isSymm_iff.mpr
      ((LinearMap.BilinForm.isSymm_iff.mp binary_symm).tmul
        (LinearMap.BilinForm.isSymm_iff.mp binary_symm))
  · simp only [LinearMap.BilinForm.tensorDistrib_tmul,
      binary_self A ha, binary_self B hb, smul_eq_mul, mul_one, ne_eq, one_ne_zero, not_false_eq_true]
  · right
    exact NeighborResidual.square_complement_unit A B ha (by omega)
  · exact hs
  · exact ht
  · exact hneigh
  · exact hh

/-- Stage two's earlier and future triple complements both have explicit
coordinate-unit witnesses, giving every actual lifted wire residual. -/
theorem second_allResiduals (P Q S T : Finset (Fin h))
    (hp : P.card = 3) (hq : Q.card = 3) (hs : S.card = 3) (ht : T.card = 3)
    (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    AllResiduals (secondGeometry (binary h) binary_symm binary_nondegenerate
      (indicator P) (triple_nonzero P hp))
      (binary h) (indicator Q) (indicator S) (indicator T) := by
  apply allResiduals_of_witnesses _ rfl
  · right
    exact NeighborResidual.triple_complement_unit P hp (by omega)
  · exact binary_symm
  · exact triple_nonzero Q hq
  · right
    exact NeighborResidual.triple_complement_unit Q hq (by omega)
  · exact hs
  · exact ht
  · exact hneigh
  · exact hh

/-- Stage three's earlier two-triple complement has an explicit tensor unit;
the empty future factor contributes a zero scratch-sink residual. -/
theorem third_allResiduals (P Q S T : Finset (Fin h))
    (hp : P.card = 3) (hq : Q.card = 3) (hs : S.card = 3) (ht : T.card = 3)
    (hneigh : Even (S ∩ T).card) (hh : 6 < h) :
    AllResiduals (thirdGeometry (binary h) binary_symm binary_nondegenerate
      (indicator P) (indicator Q) (triple_nonzero P hp) (triple_nonzero Q hq))
      unitForm (1 : ZMod 2) (indicator S) (indicator T) := by
  apply allResiduals_of_witnesses _ rfl
  · right
    exact NeighborResidual.square_complement_unit P Q hp (by omega)
  · exact unit_symm
  · simp [unitForm]
  · left
    rw [scalar_line_one, unit_orthogonal_top]
  · exact hs
  · exact ht
  · exact hneigh
  · exact hh
end Stages
end IntegerMultBounds.Networks.BinaryMotifResiduals
