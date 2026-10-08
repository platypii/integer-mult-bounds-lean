import IntegerMultBounds.Networks.GlobalLabelsResiduals
import IntegerMultBounds.Networks.GlobalProjectionRank

/-! Residual witnesses for actual sparse physical binary histories. Equality
is retained explicitly so that skipped labels compose without nondegeneracy
assumptions on unrelated intermediate subspaces. -/

namespace IntegerMultBounds.Networks.GlobalBinaryResiduals

open scoped TensorProduct
open BinaryMotifResiduals GroupedFrames LabeledMotif GlobalLabels GlobalRank

section Relation
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (B : LinearMap.BilinForm (ZMod 2) E)

/-- Certified growth: equality, or inclusion with an actual norm-one vector
in the orthogonal residual. -/
def Up (U V : Submodule (ZMod 2) E) : Prop :=
  U = V ∨ (U ≤ V ∧ ∃ x : ProjectionRank.residual B U V, B x x = 1)

@[refl, simp] theorem Up.refl (U : Submodule (ZMod 2) E) : Up B U U := Or.inl rfl

theorem Up.le {U V : Submodule (ZMod 2) E} (h : Up B U V) : U ≤ V :=
  h.elim le_of_eq And.left

@[trans] theorem Up.trans {U V W : Submodule (ZMod 2) E}
    (huv : Up B U V) (hvw : Up B V W) : Up B U W := by
  rcases huv with rfl | ⟨hle, x, hx⟩
  · exact hvw
  · exact Or.inr ⟨hle.trans (hvw.le B),
      ⟨⟨x, ⟨hvw.le B x.property.1, x.property.2⟩⟩, hx⟩⟩

theorem Up.good {U V : Submodule (ZMod 2) E} (h : Up B U V)
    (hu : (B.restrict U).Nondegenerate) : Good B (ProjectionRank.residual B U V) := by
  rcases h with rfl | ⟨_, hx⟩
  · rw [MotifResiduals.residual_self B U hu]
    exact good_bot B
  · exact Or.inr hx

theorem up_of_good [FiniteDimensional (ZMod 2) E] (hs : B.IsSymm)
    {U V : Submodule (ZMod 2) E} (hu : (B.restrict U).Nondegenerate) (hle : U ≤ V)
    (hgood : Good B (ProjectionRank.residual B U V)) : Up B U V := by
  rcases hgood with hz | hx
  · left
    have he := ProjectionRank.residual_sup B hs U V hu hle
    simpa only [hz, sup_bot_eq] using he
  · exact Or.inr ⟨hle, hx⟩

/-- Either direction of certified growth is allowed for a physical edge. -/
def Edge (U V : Submodule (ZMod 2) E) : Prop := Up B U V ∨ Up B V U

@[refl, simp] theorem Edge.refl (U : Submodule (ZMod 2) E) : Edge B U U := Or.inl (Up.refl B U)

theorem Up.edge {U V : Submodule (ZMod 2) E} (h : Up B U V) : Edge B U V := Or.inl h

theorem Up.edge_rev {U V : Submodule (ZMod 2) E} (h : Up B U V) : Edge B V U := Or.inr h

variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]

theorem up_transport (C : LinearMap.BilinForm (ZMod 2) F) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ x y, C (e x) (e y) = B x y) {U V : Submodule (ZMod 2) E}
    (h : Up B U V) : Up C (LabelTransport.label e U) (LabelTransport.label e V) := by
  rcases h with rfl | ⟨hle, x, hx⟩
  · exact Up.refl _ _
  · right
    refine ⟨Submodule.map_mono hle, ?_⟩
    rw [← LabelTransport.residual B C e he U V]
    exact ⟨⟨e x, (LabelTransport.mem_label e _ x).mpr x.property⟩, (he x x).trans hx⟩

theorem up_transport_top (C : LinearMap.BilinForm (ZMod 2) F) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ x y, C (e x) (e y) = B x y) {U : Submodule (ZMod 2) E}
    (h : Up B U ⊤) : Up C (LabelTransport.label e U) ⊤ := by
  have hp := up_transport B C e he h
  have ht : LabelTransport.label e ⊤ = ⊤ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨y, rfl⟩ := e.surjective x
      exact (LabelTransport.mem_label e ⊤ y).mpr Submodule.mem_top
  rwa [ht] at hp

end Relation

section Local
variable {h : ℕ} {E R : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c : ℕ}
  (g : MotifLabels.Geometry (ZMod 2) E (Fin h → ZMod 2))
  (S : Fin n → Finset (Fin h)) (hS : ∀ i, (S i).card = 3)
  (hcurrent : g.current = Labels.binary h) (hbase : Good g.earlier g.base) (hh : 6 < h)

/-- All elementary ascending steps used by sparse histories, including their
canonical initial and final labels. -/
structure LocalSteps (t : Fin n → (Fin h → ZMod 2)) (owner target : Fin a → Fin n) : Prop where
  x_middle : ∀ i, Up g.pairing (g.xIn (t i)) (g.xMiddle (t i))
  middle_full : ∀ i, Up g.pairing (g.xMiddle (t i)) g.full
  y_common : ∀ i, Up g.pairing (g.yIn (t i)) g.common
  common_out : ∀ i, Up g.pairing g.common (g.yOut (t i))
  bot_y : ∀ i, Up g.pairing ⊥ (g.yIn (t i))
  out_full : ∀ i, Up g.pairing (g.yOut (t i)) g.full
  bot_common : Up g.pairing ⊥ g.common
  common_full : Up g.pairing g.common g.full
  side_middle : ∀ p, Up g.pairing (g.yIn (t (target p))) (g.xMiddle (t (owner p)))
  side_out : ∀ p, Up g.pairing (g.xMiddle (t (owner p))) (g.yOut (t (target p)))

include hcurrent hbase hh hS in
omit [CommRing R] [DecidableEq R] [Nontrivial R] in
/-- Binary triple supports discharge the complete local ascending-step table. -/
theorem localSteps (owner target : Fin a → Fin n)
    (hneigh : ∀ p, Even (S (owner p) ∩ S (target p)).card) :
    LocalSteps g (fun i => Labels.indicator (S i)) owner target := by
  have ht (i) : g.current (Labels.indicator (S i)) (Labels.indicator (S i)) ≠ 0 := by
    rw [hcurrent, Labels.binary_self _ (hS i)]
    exact one_ne_zero
  have hp : ∃ v : g.past, g.earlier v v = 1 := line_unit _ _ g.p_norm
  have hc (i) : ∃ v : g.current.orthogonal ((ZMod 2) ∙ Labels.indicator (S i)),
      g.current v v = 1 := by
    rw [hcurrent]
    exact NeighborResidual.triple_complement_unit _ (hS i) (by omega)
  have hf : ∃ v : (⊤ : Submodule (ZMod 2) (Fin h → ZMod 2)), g.current v v = 1 := by
    refine ⟨⟨Pi.single ⟨0, by omega⟩ 1, Submodule.mem_top⟩, ?_⟩
    rw [hcurrent]
    exact NeighborResidual.coordinate_norm _
  constructor
  · intro i
    apply up_of_good _ g.pairing_symm (g.xIn_nondegenerate _ (ht i)) (g.xIn_le_middle _)
    rw [MotifResiduals.Geometry.xIn_middle g _ (ht i)]
    exact good_tensor _ _ hbase (Or.inr (hc i))
  · intro i
    apply up_of_good _ g.pairing_symm (g.xMiddle_nondegenerate _ (ht i)) (g.middle_le_full _)
    rw [MotifResiduals.Geometry.middle_full g _ (ht i)]
    exact Or.inr (unit_tensor _ _ hp (hc i))
  · intro i
    apply up_of_good _ g.pairing_symm (g.yIn_nondegenerate _ (ht i)) (g.yIn_le_common _)
    rw [MotifResiduals.Geometry.yIn_common g _ (ht i)]
    exact good_tensor _ _ hbase (Or.inr (hc i))
  · intro i
    apply up_of_good _ g.pairing_symm g.common_nondegenerate (g.common_le_yOut _)
    rw [MotifResiduals.Geometry.common_yOut]
    exact Or.inr (unit_tensor _ _ hp (hc i))
  · intro i
    apply up_of_good _ g.pairing_symm (MotifLabels.bot_nondegenerate _) bot_le
    rw [MotifResiduals.residual_bot]
    exact good_tensor _ _ hbase (Or.inr (line_unit _ _ (ht i)))
  · intro i
    apply up_of_good _ g.pairing_symm (g.yOut_nondegenerate _ (ht i)) (g.yOut_le_full _)
    rw [MotifResiduals.Geometry.yOut_full g _ (ht i)]
    exact Or.inr (unit_tensor _ _ hp (line_unit _ _ (ht i)))
  · apply up_of_good _ g.pairing_symm (MotifLabels.bot_nondegenerate _) bot_le
    rw [MotifResiduals.residual_bot]
    exact good_tensor _ _ hbase (Or.inr hf)
  · apply up_of_good _ g.pairing_symm g.common_nondegenerate g.common_le_full
    rw [g.central_residual_eq]
    exact Or.inr (unit_tensor _ _ hp hf)
  · intro p
    apply up_of_good _ g.pairing_symm (g.yIn_nondegenerate _ (ht _))
      ((g.yIn_le_common _).trans le_sup_left)
    exact tableEdges_good g hcurrent hbase _ _ (hS _) (hS _) (hneigh p) hh
      (g.yIn (Labels.indicator (S (target p))), g.xMiddle (Labels.indicator (S (owner p))))
      (by simp [tableEdges])
  · intro p
    have hxy : g.current (Labels.indicator (S (owner p))) (Labels.indicator (S (target p))) = 0 := by
      rw [hcurrent]
      exact Labels.binary_neighbors _ _ (hneigh p)
    apply up_of_good _ g.pairing_symm (g.xMiddle_nondegenerate _ (ht _)) (g.side_middle_le_out _ _ hxy)
    exact tableEdges_good g hcurrent hbase _ _ (hS _) (hS _) (hneigh p) hh
      (g.xMiddle (Labels.indicator (S (owner p))), g.yOut (Labels.indicator (S (target p))))
      (by simp [tableEdges])

end Local

section Histories
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Coverage of the exact sparse list and its missing endpoint gaps. -/
structure PathCertificate (B : LinearMap.BilinForm (ZMod 2) E)
    (initial final : Submodule (ZMod 2) E) (labels : List (Submodule (ZMod 2) E)) : Prop where
  edges : pathRel (Edge B) initial labels
  lower : ∀ U ∈ labels, Up B initial U
  upper : ∀ U ∈ labels, Up B U final
  endpoints : Up B initial final

variable {h n a c : ℕ} {R : Type*} [CommRing R] [DecidableEq R] [Nontrivial R]
  (g : MotifLabels.Geometry (ZMod 2) E (Fin h → ZMod 2))
  (t : Fin n → (Fin h → ZMod 2)) (owner : Fin a → Fin n)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (target : Fin a → Fin n) (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)

include hJ

/-- The forward certificate inspects actual scalar-incidence histories, so
empty columns and absent copy incidences are covered. -/
theorem forward_certificate (hs : LocalSteps g t owner target) (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (input g t i) (output g t i)
      (history (forward g t owner G J H) i) := by
  rcases i with i | i | i | i | i
  · change PathCertificate _ (g.xIn (t i)) ⊤ (history _ (Circuit.x i))
    rw [forward_x_history, ← g.full_eq_top]
    have h₁ := hs.x_middle i
    have h₂ := hs.middle_full i
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;>
      simp_all [pathRel, Up.edge]
  · change PathCertificate _ (g.yIn (t i)) (g.yOut (t i)) (history _ (Circuit.y i))
    rw [forward_y_history]
    have h₁ := hs.y_common i
    have h₂ := hs.common_out i
    have h₃ := h₁.trans _ h₂
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.side i))
    rw [forward_side_history g t owner G J H target hJ, ← g.full_eq_top]
    have h₁ := hs.bot_y (target i)
    have h₂ := hs.side_middle i
    have h₃ := hs.side_out i
    have h₄ := hs.out_full (target i)
    have h₁₂ := h₁.trans _ h₂
    have h₁₂₃ := h₁₂.trans _ h₃
    have h₁₂₃₄ := h₁₂₃.trans _ h₄
    have h₃₄ := h₃.trans _ h₄
    have h₂₃₄ := h₂.trans _ h₃₄
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.center i))
    rw [forward_center_history, ← g.full_eq_top]
    have h₁ := hs.bot_common
    have h₂ := hs.common_full
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge, Up.edge_rev]
  · exact Fin.elim0 i

/-- Logical inverse coverage includes columns whose physical full-label
incidences are both absent. -/
theorem inverse_certificate (hs : LocalSteps g t target owner) (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (inverseInput g t i)
      (output g t (Circuit.exchangeRoles n a c 0 i))
      (history (inverse g t owner G J H) i) := by
  rcases i with i | i | i | i | i
  · change PathCertificate _ (g.yIn (t i)) (g.yOut (t i)) (history _ (Circuit.x i))
    rw [inverse_x_history]
    have h₁ := hs.y_common i
    have h₂ := hs.common_out i
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ (g.xIn (t i)) ⊤ (history _ (Circuit.y i))
    rw [inverse_y_history, ← g.full_eq_top]
    have h₁ := hs.x_middle i
    have h₂ := hs.middle_full i
    have h₃ := h₁.trans _ h₂
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.side i))
    rw [inverse_side_history g t owner G J H target hJ, ← g.full_eq_top]
    have h₁ := hs.bot_y (owner i)
    have h₂ := hs.side_middle i
    have h₃ := hs.side_out i
    have h₄ := hs.out_full (owner i)
    have h₁₂ := h₁.trans _ h₂
    have h₁₂₃ := h₁₂.trans _ h₃
    have h₁₂₃₄ := h₁₂₃.trans _ h₄
    have h₃₄ := h₃.trans _ h₄
    have h₂₃₄ := h₂.trans _ h₃₄
    constructor <;> simp_all [pathRel, Up.edge]
  · change PathCertificate _ ⊥ ⊤ (history _ (Circuit.center i))
    rw [inverse_center_history, ← g.full_eq_top]
    have h₁ := hs.bot_common
    have h₂ := hs.common_full
    have h₃ := h₁.trans _ h₂
    split_ifs <;> constructor <;> simp_all [pathRel, Up.edge, Up.edge_rev]
  · exact Fin.elim0 i

/-- Renaming the inverse bank names gives the actual physical middle-stage
history, with the same certified endpoint gaps. -/
theorem opposite_certificate (hs : LocalSteps g t target owner) (i : Circuit.Role n a c 0) :
    PathCertificate g.pairing (input g t i) (output g t i)
      (history (opposite g t owner G J H) i) := by
  obtain ⟨i, rfl⟩ := (Circuit.exchangeRoles n a c 0).surjective i
  rw [opposite_history]
  have he : input g t (Circuit.exchangeRoles n a c 0 i) = inverseInput g t i := by
    rcases i with i | i | i <;> rfl
  rw [he]
  exact inverse_certificate g t owner G J H target hJ hs i

end Histories
section Transport
variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  (B : LinearMap.BilinForm (ZMod 2) E) (C : LinearMap.BilinForm (ZMod 2) F)

/-- Tensoring with a norm-one future line preserves certified growth. -/
theorem up_lift (q : F) (hq : C q q ≠ 0) {U V : Submodule (ZMod 2) E}
    (h : Up B U V) : Up (TensorSubspace.form B C)
      (TensorSubspace.space U ((ZMod 2) ∙ q)) (TensorSubspace.space V ((ZMod 2) ∙ q)) := by
  rcases h with rfl | ⟨hle, hx⟩
  · exact Up.refl _ _
  · obtain ⟨z, hz⟩ := unit_tensor B C hx (line_unit C q hq)
    refine Or.inr ⟨TensorSubspace.mono hle le_rfl, ⟨⟨z, ?_⟩, hz⟩⟩
    exact ⟨TensorSubspace.mono inf_le_left le_rfl z.property,
      TensorSubspace.orthogonal_left B C _ _ inf_le_right z.property⟩

/-- A certificate transports through any map preserving certified growth. -/
theorem PathCertificate.map (f : Submodule (ZMod 2) E → Submodule (ZMod 2) F)
    (hf : ∀ U V, Up B U V → Up C (f U) (f V))
    {initial final : Submodule (ZMod 2) E} {labels : List (Submodule (ZMod 2) E)}
    (hp : PathCertificate B initial final labels) :
    PathCertificate C (f initial) (f final) (labels.map f) := by
  constructor
  · exact pathRel_map (Edge B) (Edge C) f
      (fun _ _ h => h.elim (fun h => Or.inl (hf _ _ h)) (fun h => Or.inr (hf _ _ h)))
      initial labels hp.edges
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hU
    exact hf _ _ (hp.lower V hV)
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hU
    exact hf _ _ (hp.upper V hV)
  · exact hf _ _ hp.endpoints

omit C [AddCommGroup F] [Module (ZMod 2) F] in
/-- Earlier sparse stages may leave a smaller label, but its certified gap
composes with the first actual incidence. -/
theorem PathCertificate.weak_start {initial final actual : Submodule (ZMod 2) E}
    {labels : List (Submodule (ZMod 2) E)} (hp : PathCertificate B initial final labels)
    (ha : Up B actual initial) : PathCertificate B actual final labels := by
  constructor
  · cases labels with
    | nil => trivial
    | cons U us => exact ⟨Or.inl (ha.trans B (hp.lower U (by simp))), hp.edges.2⟩
  · exact fun U hU => ha.trans B (hp.lower U hU)
  · exact hp.upper
  · exact ha.trans B hp.endpoints

omit C [AddCommGroup F] [Module (ZMod 2) F] in
theorem PathCertificate.finish {initial final : Submodule (ZMod 2) E}
    {labels : List (Submodule (ZMod 2) E)} (hp : PathCertificate B initial final labels) :
    Up B (labels.getLast?.getD initial) final := by
  cases he : labels.getLast? with
  | none =>
    simpa only [he, Option.getD_none] using hp.endpoints
  | some U =>
    simpa only [he, Option.getD_some] using hp.upper U (List.mem_of_getLast? he)

end Transport
section CubeTransport
variable {F B : Type*} [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
  (D : LinearMap.BilinForm (ZMod 2) F) (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

omit [FiniteDimensional (ZMod 2) F] in
include ht in
theorem firstLabel_up (q : B × B) {U V : Submodule (ZMod 2) ((ZMod 2) ⊗[ZMod 2] F)}
    (hu : Up (TensorSubspace.form StageLabels.unitForm D) U V) :
    Up (GlobalProjectionRank.cubeForm D) (firstLabel t q U) (firstLabel t q V) := by
  apply up_transport (TensorSubspace.form (TensorSubspace.form StageLabels.unitForm D)
    (TensorSubspace.form D D)) (GlobalProjectionRank.cubeForm D)
    (StageLabels.firstEquiv (K := ZMod 2) (F := F)) (StageLabels.first_pairing D)
  exact up_lift _ _ _ (by
    simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
      mul_ne_zero (ht q.2) (ht q.1)) hu

omit [FiniteDimensional (ZMod 2) F] in
include ht in
theorem secondLabel_up (q : B × B) {U V : Submodule (ZMod 2) (F ⊗[ZMod 2] F)}
    (hu : Up (TensorSubspace.form D D) U V) :
    Up (GlobalProjectionRank.cubeForm D) (secondLabel t q U) (secondLabel t q V) := by
  apply up_transport _ _ StageLabels.secondEquiv (StageLabels.second_pairing D)
  exact up_lift _ D _ (ht q.2) hu

omit [FiniteDimensional (ZMod 2) F] in
theorem thirdLabel_up (q : B × B) {U V : Submodule (ZMod 2) ((F ⊗[ZMod 2] F) ⊗[ZMod 2] F)}
    (hu : Up (TensorSubspace.form (TensorSubspace.form D D) D) U V) :
    Up (GlobalProjectionRank.cubeForm D)
      (thirdLabel (K := ZMod 2) (F := F) q U) (thirdLabel (K := ZMod 2) (F := F) q V) := by
  apply up_transport (TensorSubspace.form (TensorSubspace.form (TensorSubspace.form D D) D)
    StageLabels.unitForm) (GlobalProjectionRank.cubeForm D)
    (StageLabels.thirdEquiv (K := ZMod 2) (F := F)) (StageLabels.third_pairing D)
  exact up_lift _ StageLabels.unitForm _ (by simp [StageLabels.unitForm]) hu
end CubeTransport

section Placed
variable {ι κ E F R : Type*} [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup F] [Module (ZMod 2) F]
  [CommRing R] [DecidableEq R]
  (B : LinearMap.BilinForm (ZMod 2) E) (C : LinearMap.BilinForm (ZMod 2) F)
  (f : ι ↪ κ) (labelMap : Submodule (ZMod 2) E → Submodule (ZMod 2) F)
  (hf : ∀ U V, Up B U V → Up C (labelMap U) (labelMap V))
  (localInput localOutput : ι → Submodule (ZMod 2) E)
  (current : κ → Submodule (ZMod 2) F)
  (hi : ∀ i, Up C (current (f i)) (labelMap (localInput i)))
  (vs : List (Vertex ι (Submodule (ZMod 2) E) R))
  (hc : ∀ i, PathCertificate B (localInput i) (localOutput i) (history vs i))

include hf hi hc in
theorem placed_certificate (i : ι) :
    PathCertificate C (current (f i)) (labelMap (localOutput i))
      (history (placeList f labelMap vs) (f i)) := by
  rw [history_place]
  exact ((hc i).map B C labelMap hf).weak_start C (hi i)

include hf hi hc in
theorem placed_edges :
    ∀ p ∈ RankTrace.edges current (updates (placeList f labelMap vs)), Edge C p.1 p.2 := by
  apply edges_history_rel (Edge C) (Edge.refl C)
  intro k
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i, rfl⟩ := hk
    exact (placed_certificate B C f labelMap hf localInput localOutput current hi vs hc i).edges
  · rw [history_place_outside f labelMap vs k (by simpa using hk)]
    trivial

include hf hi hc in
theorem placed_finish (i : ι) :
    Up C (finalLabels current (placeList f labelMap vs) (f i)) (labelMap (localOutput i)) := by
  rw [finalLabels_history]
  exact (placed_certificate B C f labelMap hf localInput localOutput current hi vs hc i).finish C
end Placed

section Scratch
variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]

/-- A full earlier factor exposes the actual future-line complement. -/
theorem up_tensor_top (B : LinearMap.BilinForm (ZMod 2) E) (hsB : B.IsSymm) (hnB : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) F) (hsC : C.IsSymm) (q : F) (hq : C q q ≠ 0)
    (hB : Good B ⊤) (hfuture : Good C (C.orthogonal ((ZMod 2) ∙ q))) :
    Up (TensorSubspace.form B C) (TensorSubspace.space ⊤ ((ZMod 2) ∙ q)) ⊤ := by
  apply up_of_good _ (LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp hsB).tmul (LinearMap.BilinForm.isSymm_iff.mp hsC)))
    (TensorSubspace.nondegenerate B C _ _ (MotifLabels.top_nondegenerate B hnB)
      (Labels.line_nondegenerate C q hq)) le_top
  rw [← TensorSubspace.top_top (K := ZMod 2) (E := E) (F := F),
    MotifResiduals.residual_tensor_right B C hsC _ _ _ (MotifLabels.top_nondegenerate B hnB)
      (Labels.line_nondegenerate C q hq) le_top]
  simpa only [ProjectionRank.residual, top_inf_eq] using good_tensor B C hB hfuture

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F] in
theorem good_tensor_top (B : LinearMap.BilinForm (ZMod 2) E) (C : LinearMap.BilinForm (ZMod 2) F)
    (hB : Good B ⊤) (hC : Good C ⊤) : Good (TensorSubspace.form B C) ⊤ := by
  simpa only [TensorSubspace.top_top] using good_tensor B C hB hC

end Scratch

section BinaryStages
variable {h : ℕ} {B A C R : Type*} [DecidableEq B] [DecidableEq A] [DecidableEq C]
  [CommRing R] [DecidableEq R] [Nontrivial R] {n a c : ℕ}
  (S : B → Finset (Fin h)) (hS : ∀ b, (S b).card = 3) (hh : 6 < h)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (target : Fin a → Fin n) (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
  (hneigh : ∀ p, Even (S (eB (owner p)) ∩ S (eB (target p))).card)

abbrev binarySymm : (Labels.binary h).IsSymm := ⟨Labels.form_symm 0⟩
abbrev vectors : B → (Fin h → ZMod 2) := fun b => Labels.indicator (S b)

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS in
theorem binaryNorm (b : B) : Labels.binary h (vectors S b) (vectors S b) ≠ 0 := by
  rw [Labels.binary_self _ (hS b)]
  exact one_ne_zero

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS hh hneigh in
theorem first_steps :
    LocalSteps (StageLabels.firstGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate)
      (vectors S ∘ eB) owner target := by
  apply localSteps _ (S ∘ eB) (fun i => hS (eB i)) rfl _ hh owner target hneigh
  left
  change (StageLabels.unitForm : LinearMap.BilinForm (ZMod 2) (ZMod 2)).orthogonal
    ((ZMod 2) ∙ (1 : ZMod 2)) = ⊥
  rw [StageLabels.scalar_line_one, StageLabels.unit_orthogonal_top]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS hh hneigh in
theorem second_steps (q : B × B) :
    LocalSteps (StageLabels.secondGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S q.1) (binaryNorm S hS q.1)) (vectors S ∘ eB) target owner := by
  apply localSteps _ (S ∘ eB) (fun i => hS (eB i)) rfl _ hh target owner
    (fun p => by simpa only [Function.comp_apply, Finset.inter_comm] using hneigh p)
  exact Or.inr (NeighborResidual.triple_complement_unit _ (hS q.1) (by omega))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS hh hneigh in
theorem third_steps (q : B × B) :
    LocalSteps (StageLabels.thirdGeometry (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S q.1) (vectors S q.2) (binaryNorm S hS q.1) (binaryNorm S hS q.2))
      (vectors S ∘ eB) owner target := by
  apply localSteps _ (S ∘ eB) (fun i => hS (eB i)) rfl _ hh owner target hneigh
  exact Or.inr (NeighborResidual.square_complement_unit _ _ (hS q.1) (by omega))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hh in
theorem binary_top : Good (Labels.binary h) ⊤ := by
  exact Or.inr ⟨⟨Pi.single ⟨0, by omega⟩ 1, Submodule.mem_top⟩, NeighborResidual.coordinate_norm _⟩

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS hh in
theorem first_scratch (q : B × B) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (firstLabel (vectors S) q ⊤) ⊤ := by
  apply up_transport_top (TensorSubspace.form (TensorSubspace.form StageLabels.unitForm (Labels.binary h))
    (TensorSubspace.form (Labels.binary h) (Labels.binary h))) _
    (StageLabels.firstEquiv (K := ZMod 2) (F := Fin h → ZMod 2)) (StageLabels.first_pairing _)
  apply up_tensor_top _ (LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp StageLabels.unit_symm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp binarySymm)))
    (Labels.tmul_nondegenerate _ _ StageLabels.unit_nondegenerate Labels.binary_nondegenerate)
    _ (LinearMap.BilinForm.isSymm_iff.mpr
      ((LinearMap.BilinForm.isSymm_iff.mp binarySymm).tmul
        (LinearMap.BilinForm.isSymm_iff.mp binarySymm))) _
  · simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
      mul_ne_zero (binaryNorm S hS q.2) (binaryNorm S hS q.1)
  · apply good_tensor_top _ _ _ (binary_top hh)
    exact Or.inr ⟨⟨1, Submodule.mem_top⟩, by simp [StageLabels.unitForm]⟩
  · exact Or.inr (NeighborResidual.square_complement_unit _ _ (hS q.1) (by omega))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hS hh in
theorem second_scratch (q : B × B) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (secondLabel (vectors S) q ⊤) ⊤ := by
  apply up_transport_top _ _ StageLabels.secondEquiv (StageLabels.second_pairing (Labels.binary h))
  exact up_tensor_top _ (LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp binarySymm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp binarySymm)))
    (Labels.tmul_nondegenerate _ _ Labels.binary_nondegenerate Labels.binary_nondegenerate)
    _ binarySymm _ (binaryNorm S hS q.2)
    (good_tensor_top _ _ (binary_top hh) (binary_top hh))
    (Or.inr (NeighborResidual.triple_complement_unit _ (hS q.2) (by omega)))

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
theorem third_scratch (q : B × B) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h))
      (thirdLabel (K := ZMod 2) (F := Fin h → ZMod 2) q ⊤) ⊤ := by
  left
  unfold thirdLabel MotifLabels.Geometry.liftLabel
  rw [StageLabels.scalar_line_one, TensorSubspace.top_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (StageLabels.thirdEquiv (K := ZMod 2) (F := Fin h → ZMod 2)).surjective

include hh hJ hneigh in
/-- Each real placed invocation has certified physical edges and certified
remaining output gaps, for an already certified sparse input gap. -/
theorem invocation_certificate (j : Fin 3) (q : B × B)
    (current : GlobalCircuit.World B A C → Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ i, Up (GlobalProjectionRank.cubeForm (Labels.binary h))
      (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i)) :
    (∀ p ∈ RankTrace.edges current (updates (invocation (Labels.binary h) binarySymm Labels.binary_nondegenerate
      (vectors S) (binaryNorm S hS) eB eA eC owner G J H j q)),
      Edge (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2) ∧
    (∀ i, Up (GlobalProjectionRank.cubeForm (Labels.binary h))
      (finalLabels current (invocation (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB eA eC owner G J H j q)
        (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationOutput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate
        (vectors S) (binaryNorm S hS) eB j q i)) := by
  fin_cases j
  · simp only [invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := forward_certificate _ (vectors S ∘ eB) owner G J H target hJ
      (first_steps S hS hh eB owner target hneigh)
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => firstLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => firstLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
  · simp only [invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := opposite_certificate _ (vectors S ∘ eB) owner G J H target hJ
      (second_steps S hS hh eB owner target hneigh q)
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => secondLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => secondLabel_up _ _ (binaryNorm S hS) q)
        _ _ current hcur _ hc
  · simp only [invocation, invocationInput, invocationOutput] at hcur ⊢
    have hc := forward_certificate _ (vectors S ∘ eB) owner G J H target hJ
      (third_steps S hS hh eB owner target hneigh q)
    constructor
    · exact placed_edges _ _ _ _ (fun _ _ => thirdLabel_up _ q)
        _ _ current hcur _ hc
    · exact placed_finish _ _ _ _ (fun _ _ => thirdLabel_up _ q)
        _ _ current hcur _ hc
omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
include hh in
theorem invocationOutput_up_profile (j : Fin 3) (q : B × B) (i : Circuit.Role n a c 0) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h))
      (invocationOutput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i)
      (profileOutput (A := A) (C := C) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j
        (GlobalCircuit.localEmbedding eB eA eC j q i)) := by
  rcases i with i | i | i | i | i
  · by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
      simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap,
        GlobalCircuit.address, invocationOutput, xOutput, output,
        MotifLabels.Geometry.full_eq_top, h₀, h₁]
  · by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
      simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap,
        GlobalCircuit.address, invocationOutput, yOutput, output, h₀, h₁]
  · change Up _ (invocationOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q (Circuit.side i)) _
    simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.side]
    by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
      simp only [invocationOutput, output, h₀, h₁, ↓reduceIte]
    all_goals first | exact first_scratch S hS hh q | exact second_scratch S hS hh q | exact third_scratch q
  · change Up _ (invocationOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q (Circuit.center i)) _
    simp [profileOutput, GlobalCircuit.localEmbedding, GlobalCircuit.localMap, Circuit.center]
    by_cases h₀ : j = 0 <;> by_cases h₁ : j = 1 <;>
      simp only [invocationOutput, output, h₀, h₁, ↓reduceIte]
    all_goals first | exact first_scratch S hS hh q | exact second_scratch S hS hh q | exact third_scratch q
  · exact Fin.elim0 i

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [DecidableEq R] [Nontrivial R] in
include hh in
theorem cube_bot_top : Up (GlobalProjectionRank.cubeForm (Labels.binary h))
    (⊥ : Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2))) ⊤ := by
  right
  refine ⟨bot_le, ?_⟩
  rw [MotifResiduals.residual_bot]
  let z : Fin h → ZMod 2 := Pi.single ⟨0, by omega⟩ 1
  refine ⟨⟨z ⊗ₜ[ZMod 2] (z ⊗ₜ[ZMod 2] z), Submodule.mem_top⟩, ?_⟩
  simp only [GlobalProjectionRank.cubeForm, LinearMap.BilinForm.tensorDistrib_tmul,
    NeighborResidual.coordinate_norm, smul_eq_mul, mul_one, z]

omit [DecidableEq B] [DecidableEq A] [DecidableEq C] in
include hh hneigh in
theorem profileInput_up_output (j : Fin 3) (k : GlobalCircuit.World B A C) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h))
      (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j k) (profileOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j k) := by
  rcases k with b | b | p
  · change Up _ (xInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j b) (xOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j b)
    fin_cases j <;> simp [xInput, xOutput]
    · have hc := first_steps S hS hh eB owner target hneigh
      have hp := (hc.x_middle (eB.symm b.1)).trans _ (hc.middle_full (eB.symm b.1))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        firstLabel_up (Labels.binary h) (vectors S) (binaryNorm S hS) (b.2.1, b.2.2) hp
    · have hc := second_steps S hS hh eB owner target hneigh (b.1, b.2.2)
      have hp := (hc.x_middle (eB.symm b.2.1)).trans _ (hc.middle_full (eB.symm b.2.1))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        secondLabel_up (Labels.binary h) (vectors S) (binaryNorm S hS) (b.1, b.2.2) hp
    · have hc := third_steps S hS hh eB owner target hneigh (b.1, b.2.1)
      have hp := (hc.x_middle (eB.symm b.2.2)).trans _ (hc.middle_full (eB.symm b.2.2))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        thirdLabel_up (Labels.binary h) (b.1, b.2.1) hp
  · change Up _ (yInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j b) (yOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j b)
    fin_cases j <;> simp [yInput, yOutput]
    · have hc := first_steps S hS hh eB owner target hneigh
      have hp := (hc.y_common (eB.symm b.1)).trans _ (hc.common_out (eB.symm b.1))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        firstLabel_up (Labels.binary h) (vectors S) (binaryNorm S hS) (b.2.1, b.2.2) hp
    · have hc := second_steps S hS hh eB owner target hneigh (b.1, b.2.2)
      have hp := (hc.y_common (eB.symm b.2.1)).trans _ (hc.common_out (eB.symm b.2.1))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        secondLabel_up (Labels.binary h) (vectors S) (binaryNorm S hS) (b.1, b.2.2) hp
    · have hc := third_steps S hS hh eB owner target hneigh (b.1, b.2.1)
      have hp := (hc.y_common (eB.symm b.2.2)).trans _ (hc.common_out (eB.symm b.2.2))
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        thirdLabel_up (Labels.binary h) (b.1, b.2.1) hp
  · change Up _ (if p.1.1 < j then ⊤ else ⊥) (if p.1.1 ≤ j then ⊤ else ⊥)
    split_ifs with h₁ h₂ h₂
    · exact Up.refl _ _
    · exact (h₂ (le_of_lt h₁)).elim
    · exact cube_bot_top hh
    · exact Up.refl _ _

include hh hJ hneigh in
/-- Disjoint physical placements preserve the residual certificate of each
actual invocation while the other fixed-coordinate keys execute. -/
theorem partial_edges (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ q ∈ qs, ∀ i, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i)) :
    ∀ p ∈ RankTrace.edges current
      (updates (qs.flatMap (invocation (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j))), Edge (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2 := by
  induction qs generalizing current with
  | nil => simp [updates, RankTrace.edges]
  | cons q qs ih =>
    have hnodup := List.nodup_cons.mp hq
    have hrest : ∀ q' ∈ qs, ∀ i, Up (GlobalProjectionRank.cubeForm (Labels.binary h))
        (finalLabels current (invocation (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j q)
          (GlobalCircuit.localEmbedding eB eA eC j q' i))
        (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q' i) := by
      intro q' hq' i
      rw [invocation_final_outside (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j q current _]
      · exact hcur q' (by simp [hq']) i
      · intro i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    intro p hp
    rw [List.flatMap_cons, updates_append, RankTrace.edges_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact (invocation_certificate S hS hh eB eA eC owner G J H target hJ hneigh
        j q current (hcur q (by simp))).1 p hp
    · rw [← finalLabels_trace] at hp
      exact ih hnodup.2 _ hrest p hp

include hh hJ hneigh in
theorem partial_finish (j : Fin 3) (qs : List (B × B)) (hq : qs.Nodup)
    (current : GlobalCircuit.World B A C → Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ q ∈ qs, ∀ i, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (current (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i))
    (q : B × B) (hmem : q ∈ qs) (i : Circuit.Role n a c 0) :
    Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (finalLabels current (qs.flatMap (invocation (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j))
      (GlobalCircuit.localEmbedding eB eA eC j q i))
      (invocationOutput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i) := by
  induction qs generalizing current with
  | nil => simp at hmem
  | cons q' qs ih =>
    have hnodup := List.nodup_cons.mp hq
    rw [List.flatMap_cons, finalLabels_append]
    by_cases he : q = q'
    · subst q'
      rw [partial_final_outside (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j qs _ _]
      · exact (invocation_certificate S hS hh eB eA eC owner G J H target hJ hneigh
          j q current (hcur q (by simp))).2 i
      · intro q' hq' i'
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q'; exact hnodup.1 hq') i' i
    · apply ih hnodup.2 _ _ ((List.mem_cons.mp hmem).resolve_left he)
      intro q'' hq'' i'
      rw [invocation_final_outside (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j q' current _]
      · exact hcur q'' (by simp [hq'']) i'
      · intro i''
        exact localEmbedding_disjoint eB eA eC j (by intro he; subst q''; exact hnodup.1 hq'') i'' i'

include hh hJ hneigh in
/-- Complete coverage and output-gap propagation for a real physical stage. -/
theorem stage_certificate (j : Fin 3)
    (current : GlobalCircuit.World B A C → Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)))
    (hcur : ∀ k, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (current k) (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j k)) :
    (∀ p ∈ RankTrace.edges current (updates (stage (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j)), Edge (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2) ∧
    (∀ k, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (finalLabels current (stage (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j) k)
      (profileOutput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) j k)) := by
  have hi : ∀ q ∈ GlobalCircuit.keys eB, ∀ i,
      Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (current (GlobalCircuit.localEmbedding eB eA eC j q i))
        (invocationInput (a := a) (c := c) (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB j q i) := by
    intro q _ i
    rw [← profileInput_local (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC j q i]
    exact hcur _
  constructor
  · exact partial_edges S hS hh eB eA eC owner G J H target hJ hneigh
      j _ (GlobalCircuit.keys_nodup eB) current hi
  · intro k
    by_cases hk : ∃ q i, GlobalCircuit.localEmbedding eB eA eC j q i = k
    · obtain ⟨q, i, rfl⟩ := hk
      exact (partial_finish S hS hh eB eA eC owner G J H target hJ hneigh
        j _ (GlobalCircuit.keys_nodup eB) current hi q (GlobalCircuit.mem_keys eB q) i).trans _
        (invocationOutput_up_profile S hS hh eB eA eC j q i)
    · rw [stage, partial_final_outside (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H j _ current k]
      · exact (hcur k).trans _ (profileInput_up_output S hS hh eB owner target hneigh j k)
      · intro q _ i he
        exact hk ⟨q, i, he⟩

include hh hJ hneigh in
/-- All three actual stages have certified edges, and their actual final
labels retain certified gaps to the prescribed sinks. -/
theorem program_certificate :
    (∀ p ∈ RankTrace.edges (source (A := A) (C := C) (vectors S))
      (updates (program (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H)), Edge (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2) ∧
    (∀ k, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (finalLabels (source (vectors S)) (program (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H) k)
      (sink (Labels.binary h) (vectors S) k)) := by
  have h₀ := stage_certificate S hS hh eB eA eC owner G J H target hJ hneigh 0 (source (vectors S))
    (fun k => by rw [profile_zero_source])
  have hi₁ : ∀ k, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (afterFirst (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H k) (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) 1 k) := by
    intro k
    rw [← profile_zero_one]
    exact h₀.2 k
  have h₁ := stage_certificate S hS hh eB eA eC owner G J H target hJ hneigh 1 _ hi₁
  have hi₂ : ∀ k, Up (GlobalProjectionRank.cubeForm (Labels.binary h)) (afterSecond (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H k) (profileInput (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) 2 k) := by
    intro k
    rw [← profile_one_two]
    exact h₁.2 k
  have h₂ := stage_certificate S hS hh eB eA eC owner G J H target hJ hneigh 2 _ hi₂
  dsimp [afterFirst, afterSecond] at h₁ h₂
  constructor
  · intro p hp
    simp only [program, updates_append, RankTrace.edges_append, RankTrace.finish_append,
      ← finalLabels_trace, List.mem_append, or_assoc] at hp
    rcases hp with hp | hp | hp
    · exact h₀.1 p hp
    · exact h₁.1 p hp
    · exact h₂.1 p hp
  · intro k
    rw [← profile_two_sink (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS)]
    simpa only [program, finalLabels_append] using h₂.2 k

include hh hJ hneigh in
/-- Every edge in the literal complete binary network trace has a certified
norm-one residual direction, including the actual final sink alignment. -/
theorem network_edges (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ RankTrace.edges (source (vectors S))
      (GlobalProjectionRank.trace (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H wires), Edge (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2 := by
  obtain ⟨hc, hf⟩ := program_certificate S hS hh eB eA eC owner G J H target hJ hneigh
  intro p hp
  rw [GlobalProjectionRank.trace, networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact hc p hp
  · apply edges_endpoints_rel (Edge (GlobalProjectionRank.cubeForm (Labels.binary h))) (Edge.refl _) _ _ wires _ p hp
    intro k _
    rw [← finalLabels_trace]
    exact Or.inl (hf k)

include hh hJ hneigh in
/-- Actual cube-label residual units, oriented by the proved inclusion. No
local history, endpoint gap, or nonalternation witness is an assumption. -/
theorem network_residuals (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ RankTrace.edges (source (vectors S))
      (GlobalProjectionRank.trace (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H wires),
      (p.1 ≤ p.2 ∧ Good (GlobalProjectionRank.cubeForm (Labels.binary h)) (ProjectionRank.residual (GlobalProjectionRank.cubeForm (Labels.binary h)) p.1 p.2)) ∨
      (p.2 ≤ p.1 ∧ Good (GlobalProjectionRank.cubeForm (Labels.binary h)) (ProjectionRank.residual (GlobalProjectionRank.cubeForm (Labels.binary h)) p.2 p.1)) := by
  intro p hp
  have hnd := ProjectionTrace.edges_predicate
    (fun U : Submodule (ZMod 2) (StageLabels.Ambient (ZMod 2) (Fin h → ZMod 2)) =>
      ((GlobalProjectionRank.cubeForm (Labels.binary h)).restrict U).Nondegenerate)
    (source (vectors S)) (GlobalProjectionRank.trace (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H wires)
    (GlobalProjectionRank.source_nondegenerate (Labels.binary h) (vectors S) (binaryNorm S hS))
    (GlobalProjectionRank.trace_nondegenerate (Labels.binary h) binarySymm Labels.binary_nondegenerate (vectors S) (binaryNorm S hS) eB eA eC owner G J H wires) p hp
  rcases network_edges S hS hh eB eA eC owner G J H target hJ hneigh wires p hp with h | h
  · exact Or.inl ⟨h.le _, h.good _ hnd.1⟩
  · exact Or.inr ⟨h.le _, h.good _ hnd.2⟩

end BinaryStages
end IntegerMultBounds.Networks.GlobalBinaryResiduals
