import IntegerMultBounds.Networks.ProjectionRank
import IntegerMultBounds.Networks.BinaryOrthonormal

/-! The degree-one residual between neighboring triple lines. Its dimension
and nondegeneracy are derived from actual orthogonal subspaces. Binary unit
witnesses are coordinate vectors outside the triple supports. -/

namespace IntegerMultBounds.Networks.NeighborResidual

open Module

section Pair
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (u v : E) (hu : B u u ≠ 0) (hv : B v v ≠ 0) (huv : B u v = 0)

def pairSpace : Submodule K E := (K ∙ u) ⊔ (K ∙ v)

/-- The side-wire residual from the first line into the second line's
complement is exactly the complement of their span. -/
theorem side_residual [FiniteDimensional K E] :
    ProjectionRank.residual B (K ∙ u) (B.orthogonal (K ∙ v)) =
      B.orthogonal (pairSpace u v) := by
  apply le_antisymm
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add, LinearMap.add_apply, hx.2 a ha, hx.1 b hb, add_zero]
  · intro x hx
    exact ⟨fun y hy => hx y (Submodule.mem_sup_right hy),
      fun y hy => hx y (Submodule.mem_sup_left hy)⟩

include hs hu hv huv in
theorem pair_nondegenerate : (B.restrict (pairSpace u v)).Nondegenerate := by
  have hl : (B.restrict (pairSpace u v)).SeparatingLeft := by
    rintro ⟨x, hx⟩ hxorth
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h1 := hxorth ⟨u, (show K ∙ u ≤ pairSpace u v from le_sup_left)
      (Submodule.mem_span_singleton_self u)⟩
    have h2 := hxorth ⟨v, (show K ∙ v ≤ pairSpace u v from le_sup_right)
      (Submodule.mem_span_singleton_self v)⟩
    have hvu : B v u = 0 := (hs.eq v u).trans huv
    change B (s • u + t • v) u = 0 at h1
    change B (s • u + t • v) v = 0 at h2
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, huv, hvu, mul_zero, add_zero, zero_add] at h1 h2
    have hs0 := (mul_eq_zero.mp h1).resolve_right hu
    have ht0 := (mul_eq_zero.mp h2).resolve_right hv
    apply Subtype.ext
    simp [hs0, ht0]
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  exact (hs.eq x y).trans (hx y)

include hu huv in
theorem pair_disjoint : Disjoint (K ∙ u) (K ∙ v) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy
  have he := congrArg (B u) ht
  simp only [map_smul, smul_eq_mul, huv, mul_zero] at he
  have hs0 := (mul_eq_zero.mp he.symm).resolve_right hu
  simp [hs0]

include hu hv huv in
theorem pair_finrank [FiniteDimensional K E] : finrank K (pairSpace (K := K) u v) = 2 := by
  have hu0 : u ≠ 0 := by intro h; exact hu (by simp [h])
  have hv0 : v ≠ 0 := by intro h; exact hv (by simp [h])
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ u) (K ∙ v)
  rw [(pair_disjoint B u v hu huv).eq_bot, finrank_bot,
    finrank_span_singleton hu0, finrank_span_singleton hv0, add_zero] at hd
  exact hd

include hs hu hv huv in
theorem pair_complement [FiniteDimensional K E] (hn : B.Nondegenerate) :
    (B.restrict (B.orthogonal (pairSpace u v))).Nondegenerate ∧
      finrank K (B.orthogonal (pairSpace u v)) = finrank K E - 2 := by
  refine ⟨ProjectionRank.orthogonal_nondegenerate B hs hn _
    (pair_nondegenerate B hs u v hu hv huv), ?_⟩
  rw [B.finrank_orthogonal hn, pair_finrank B u v hu hv huv]

end Pair

section Binary
open Labels
open scoped TensorProduct
variable {h : ℕ}

theorem coordinate_norm (i : Fin h) : binary h (Pi.single i 1) (Pi.single i 1) = 1 := by
  simp [binary, form_single]

theorem coordinate_orthogonal (S : Finset (Fin h)) (i : Fin h) (hi : i ∉ S) :
    Pi.single i 1 ∈ (binary h).orthogonal ((ZMod 2) ∙ indicator S) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [map_smul, LinearMap.smul_apply, binary, form_single, indicator, hi]

theorem exists_coordinate_outside (S : Finset (Fin h)) (hs : S.card < h) :
    ∃ i : Fin h, i ∉ S := by
  by_contra! hall
  have he : S = Finset.univ := Finset.eq_univ_of_forall hall
  simp [he] at hs

/-- A triple complement has an explicit unit, even in characteristic two. -/
theorem triple_complement_unit (S : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    ∃ x : (binary h).orthogonal ((ZMod 2) ∙ indicator S), binary h x x = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_outside S (by omega)
  exact ⟨⟨Pi.single i 1, coordinate_orthogonal S i hi⟩, coordinate_norm i⟩

theorem triple_complement_orthonormal (S : Finset (Fin h)) (hs : S.card = 3)
    (hh : 3 < h) :
    let W := (binary h).orthogonal ((ZMod 2) ∙ indicator S)
    ∃ b : Basis (Fin (finrank (ZMod 2) W)) (ZMod 2) W,
      ∀ i j, binary h (b i) (b j) = if i = j then 1 else 0 := by
  have hsym : (binary h).IsSymm := ⟨form_symm 0⟩
  exact BinaryOrthonormal.exists_orthonormal_basis _ (hsym.restrict _)
    (ProjectionRank.orthogonal_nondegenerate _ hsym binary_nondegenerate _
      (binary_line_nondegenerate S hs)) (triple_complement_unit S hs hh)

/-- Outside the union of two supports the coordinate unit lies in their common
orthogonal complement. The witness does not require the triples to be neighbors. -/
theorem pair_complement_unit (S T : Finset (Fin h)) (hs : S.card = 3)
    (ht : T.card = 3) (hh : 6 < h) :
    ∃ x : (binary h).orthogonal (pairSpace (indicator S) (indicator T)),
      binary h x x = 1 := by
  have hc : (S ∪ T).card < h := lt_of_le_of_lt (Finset.card_union_le S T) (by omega)
  obtain ⟨i, hi⟩ := exists_coordinate_outside (S ∪ T) hc
  have hS := coordinate_orthogonal S i (fun h => hi (Finset.mem_union_left T h))
  have hT := coordinate_orthogonal T i (fun h => hi (Finset.mem_union_right S h))
  refine ⟨⟨Pi.single i 1, ?_⟩, coordinate_norm i⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  simp only [map_add, LinearMap.add_apply, hS a ha, hT b hb, add_zero]

/-- The earlier/future two-factor line also has a unit in its complement.
The witness is an actual pure tensor of coordinate vectors. -/
theorem square_complement_unit (S T : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    let B : LinearMap.BilinForm (ZMod 2)
      ((Fin h → ZMod 2) ⊗[ZMod 2] (Fin h → ZMod 2)) := (binary h).tmul (binary h)
    let w := indicator S ⊗ₜ[ZMod 2] indicator T
    ∃ x : B.orthogonal ((ZMod 2) ∙ w), B x x = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_outside S (by omega)
  let e : Fin h → ZMod 2 := Pi.single i 1
  have hn : binary h e e = 1 := coordinate_norm i
  have ho : binary h (indicator S) e = 0 := by
    simp [e, binary, form_single, indicator, hi]
  refine ⟨⟨e ⊗ₜ[ZMod 2] e, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_smul, LinearMap.smul_apply, LinearMap.BilinForm.tmul,
      LinearMap.BilinForm.tensorDistrib_tmul, ho]
  · simp [LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, hn]

/-- The full terminal tensor-line complement has a concrete norm-one witness. -/
theorem cube_complement_unit (S T U : Finset (Fin h)) (hs : S.card = 3) (hh : 3 < h) :
    ∃ x : (cubeForm (binary h)).orthogonal ((ZMod 2) ∙ cubeVector S T U),
      cubeForm (binary h) x x = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_outside S (by omega)
  let e : Fin h → ZMod 2 := Pi.single i 1
  have hn : binary h e e = 1 := coordinate_norm i
  have ho : binary h (indicator S) e = 0 := by
    simp [e, binary, form_single, indicator, hi]
  refine ⟨⟨e ⊗ₜ[ZMod 2] (e ⊗ₜ[ZMod 2] e), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [map_smul, LinearMap.smul_apply, cubeForm, cubeVector,
      LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, ho]
  · simp [cubeForm, LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, hn]

/-- The actual neighboring-triple residual has dimension h-2 and an
orthonormal basis; its nonalternation is proved by the coordinate witness. -/
theorem binary_neighbor_residual (S T : Finset (Fin h)) (hs : S.card = 3)
    (ht : T.card = 3) (hneighbors : Even (S ∩ T).card) (hh : 6 < h) :
    let W := (binary h).orthogonal (pairSpace (indicator S) (indicator T))
    finrank (ZMod 2) W = h - 2 ∧
      ∃ b : Basis (Fin (finrank (ZMod 2) W)) (ZMod 2) W,
        ∀ i j, binary h (b i) (b j) = if i = j then 1 else 0 := by
  have hsym : (binary h).IsSymm := ⟨form_symm 0⟩
  have hSu : binary h (indicator S) (indicator S) ≠ 0 := by
    rw [binary_self S hs]; exact one_ne_zero
  have hTu : binary h (indicator T) (indicator T) ≠ 0 := by
    rw [binary_self T ht]; exact one_ne_zero
  obtain ⟨hnd, hdim⟩ := pair_complement (binary h) hsym _ _ hSu hTu
    (binary_neighbors S T hneighbors) binary_nondegenerate
  refine ⟨by simpa using hdim, ?_⟩
  exact BinaryOrthonormal.exists_orthonormal_basis _ (hsym.restrict _) hnd
    (pair_complement_unit S T hs ht hh)

end Binary

/-- Rational neighboring triples also give the exact h-2 residual, with no
positive-definiteness assumption on the corrected dot product. -/
theorem rational_neighbor_residual {h : ℕ} (S T : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hneighbors : (S ∩ T).card = 1) (hh : h ≠ 9) :
    let W := (Labels.rational h).orthogonal
      (pairSpace (Labels.indicator S) (Labels.indicator T))
    ((Labels.rational h).restrict W).Nondegenerate ∧ finrank ℚ W = h - 2 := by
  have hsym : (Labels.rational h).IsSymm := ⟨Labels.form_symm (1 / 9)⟩
  have hSu : Labels.rational h (Labels.indicator S) (Labels.indicator S) ≠ 0 := by
    rw [Labels.rational_self S hs]; norm_num
  have hTu : Labels.rational h (Labels.indicator T) (Labels.indicator T) ≠ 0 := by
    rw [Labels.rational_self T ht]; norm_num
  simpa using pair_complement (Labels.rational h) hsym _ _ hSu hTu
    (Labels.rational_neighbors S T hs ht hneighbors) (Labels.rational_nondegenerate hh)

end IntegerMultBounds.Networks.NeighborResidual
