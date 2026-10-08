import IntegerMultBounds.Networks.MotifLabels

/-! Actual associator and unit identifications for the three local tensor stages.
Subspaces are transported by the concrete tensor linear equivalences, and form
preservation is proved, not assumed. These lemmas reconcile the local motif
label table with a single right-associated three-factor ambient space. -/

namespace IntegerMultBounds.Networks.StageLabels

open scoped TensorProduct
open TensorSubspace Module

variable {K E F G : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [AddCommGroup G] [Module K G]

/-- Induction over an actual tensor subspace using its pure-tensor generators. -/
theorem space_induction {U : Submodule K E} {V : Submodule K F}
    {P : E ⊗[K] F → Prop} {x : E ⊗[K] F} (hx : x ∈ space U V)
    (hm : ∀ u ∈ U, ∀ v ∈ V, P (u ⊗ₜ[K] v))
    (ha : ∀ x y, P x → P y → P (x + y)) : P x := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.inductionOn with
  | tmul u v => exact hm u u.property v v.property
  | add x y hx hy => simpa only [map_add] using ha _ _ hx hy

theorem space_le {U : Submodule K E} {V : Submodule K F} {W : Submodule K (E ⊗[K] F)}
    (h : ∀ u ∈ U, ∀ v ∈ V, u ⊗ₜ[K] v ∈ W) : space U V ≤ W := by
  intro x hx
  exact space_induction hx h (fun _ _ => W.add_mem)

/-- Tensoring two actual lines gives the line spanned by their pure tensor. -/
theorem space_lines (u : E) (v : F) : space (K ∙ u) (K ∙ v) = K ∙ (u ⊗ₜ[K] v) := by
  apply le_antisymm
  · apply space_le
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = u ⊗ₜ[K] v := Set.mem_singleton_iff.mp hx
    subst x
    exact tmul_mem _ _ (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)

/-- Associating tensor factors transports their actual embedded subspaces. -/
theorem space_assoc (U : Submodule K E) (V : Submodule K F) (W : Submodule K G) :
    (space (space U V) W).map (TensorProduct.assoc K E F G).toLinearMap =
      space U (space V W) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply space_le
    intro uv huv w hw
    apply space_induction huv
    · intro u hu v hv
      change (TensorProduct.assoc K E F G) ((u ⊗ₜ[K] v) ⊗ₜ[K] w) ∈ space U (space V W)
      rw [TensorProduct.assoc_tmul]
      exact tmul_mem _ _ hu (tmul_mem _ _ hv hw)
    · intro x y hx hy
      change (TensorProduct.assoc K E F G) ((x + y) ⊗ₜ[K] w) ∈ space U (space V W)
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ hx hy
  · apply space_le
    intro u hu vw hvw
    apply space_induction hvw
    · intro v hv w hw
      exact ⟨(u ⊗ₜ[K] v) ⊗ₜ[K] w, tmul_mem _ _ (tmul_mem _ _ hu hv) hw,
        TensorProduct.assoc_tmul u v w⟩
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy

/-- The empty earlier factor is the scalar field, eliminated by the actual unit map. -/
theorem space_lid (U : Submodule K E) :
    (space (⊤ : Submodule K K) U).map (TensorProduct.lid K E).toLinearMap = U := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply space_le
    intro c _ u hu
    change (TensorProduct.lid K E) (c ⊗ₜ[K] u) ∈ U
    rw [TensorProduct.lid_tmul]
    exact U.smul_mem c hu
  · intro u hu
    exact ⟨(1 : K) ⊗ₜ[K] u, tmul_mem _ _ Submodule.mem_top hu, by simp⟩

/-- The empty future factor is eliminated by the right unit map. -/
theorem space_rid (U : Submodule K E) :
    (space U (⊤ : Submodule K K)).map (TensorProduct.rid K E).toLinearMap = U := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply space_le
    intro u hu c _
    change (TensorProduct.rid K E) (u ⊗ₜ[K] c) ∈ U
    rw [TensorProduct.rid_tmul]
    exact U.smul_mem c hu
  · intro u hu
    exact ⟨u ⊗ₜ[K] (1 : K), tmul_mem _ _ hu Submodule.mem_top, by simp⟩

section Congr
variable {E' F' : Type*} [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']

theorem space_congr (e : E ≃ₗ[K] E') (f : F ≃ₗ[K] F') (U : Submodule K E) (V : Submodule K F) :
    (space U V).map (TensorProduct.congr e f).toLinearMap =
      space (U.map e.toLinearMap) (V.map f.toLinearMap) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply space_le
    intro u hu v hv
    change (TensorProduct.congr e f) (u ⊗ₜ[K] v) ∈ space (U.map e.toLinearMap) (V.map f.toLinearMap)
    simp only [TensorProduct.congr_tmul]
    exact tmul_mem _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  · apply space_le
    intro u hu v hv
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨v, hv, rfl⟩ := hv
    exact ⟨u ⊗ₜ[K] v, tmul_mem _ _ hu hv, TensorProduct.congr_tmul e f u v⟩
end Congr

/-- Bilinear form on the one-dimensional empty tensor factor. -/
def unitForm : LinearMap.BilinForm K K := LinearMap.mul K K

/-- Associators are isometries for the actual tensor bilinear forms. -/
theorem assoc_pairing (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (D : LinearMap.BilinForm K G) (x y : (E ⊗[K] F) ⊗[K] G) :
    form B (form C D) ((TensorProduct.assoc K E F G) x) ((TensorProduct.assoc K E F G) y) =
      form (form B C) D x y := by
  have he : (form B (form C D)).comp (TensorProduct.assoc K E F G).toLinearMap
      (TensorProduct.assoc K E F G).toLinearMap = form (form B C) D := by
    apply TensorProduct.ext_threefold
    intro u v w
    apply TensorProduct.ext_threefold
    intro u' v' w'
    simp [LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
    ring
  exact congrArg (fun T : LinearMap.BilinForm K _ => T x y) he

theorem lid_pairing (B : LinearMap.BilinForm K E) (x y : K ⊗[K] E) :
    B ((TensorProduct.lid K E) x) ((TensorProduct.lid K E) y) = form unitForm B x y := by
  have he : B.comp (TensorProduct.lid K E).toLinearMap (TensorProduct.lid K E).toLinearMap =
      form unitForm B := by
    ext c u
    simp [LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.tensorDistrib_tmul,
      unitForm, smul_eq_mul]
  exact congrArg (fun T : LinearMap.BilinForm K _ => T x y) he

theorem rid_pairing (B : LinearMap.BilinForm K E) (x y : E ⊗[K] K) :
    B ((TensorProduct.rid K E) x) ((TensorProduct.rid K E) y) = form B unitForm x y := by
  have he : B.comp (TensorProduct.rid K E).toLinearMap (TensorProduct.rid K E).toLinearMap =
      form B unitForm := by
    ext u c
    simp [LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.tensorDistrib_tmul,
      unitForm, smul_eq_mul]
  exact congrArg (fun T : LinearMap.BilinForm K _ => T x y) he

section Isometries
variable {E' F' : Type*} [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']

theorem congr_pairing (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (B' : LinearMap.BilinForm K E') (C' : LinearMap.BilinForm K F')
    (e : E ≃ₗ[K] E') (f : F ≃ₗ[K] F')
    (he : ∀ x y, B' (e x) (e y) = B x y) (hf : ∀ x y, C' (f x) (f y) = C x y)
    (x y : E ⊗[K] F) :
    form B' C' ((TensorProduct.congr e f) x) ((TensorProduct.congr e f) y) = form B C x y := by
  have hh : (form B' C').comp (TensorProduct.congr e f).toLinearMap
      (TensorProduct.congr e f).toLinearMap = form B C := by
    ext u v u' v'
    simp [LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.tensorDistrib_tmul, he, hf]
  exact congrArg (fun T : LinearMap.BilinForm K _ => T x y) hh

/-- A proved isometry transports the actual orthogonal complement. -/
theorem map_orthogonal (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K E')
    (e : E ≃ₗ[K] E') (he : ∀ x y, C (e x) (e y) = B x y) (U : Submodule K E) :
    (B.orthogonal U).map e.toLinearMap = C.orthogonal (U.map e.toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he y x).trans (hx y hy)
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro x hx
    rw [← he, e.apply_symm_apply]
    exact hy (e x) ⟨x, hx, rfl⟩
end Isometries

/-- Zero earlier complement really yields the zero tensor subspace. -/
theorem space_bot_left (V : Submodule K F) : space (⊥ : Submodule K E) V = ⊥ := by
  apply le_antisymm _ bot_le
  apply space_le
  intro u hu v _
  have hu0 : u = 0 := by simpa using hu
  simp [hu0]

theorem scalar_line_one : (K ∙ (1 : K)) = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.mem_span_singleton.mpr ⟨x, by simp⟩

theorem unit_orthogonal_top : (unitForm : LinearMap.BilinForm K K).orthogonal ⊤ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have h := hx 1 Submodule.mem_top
  simpa [unitForm] using h

abbrev Ambient (K F : Type*) [Field K] [AddCommGroup F] [Module K F] := F ⊗[K] (F ⊗[K] F)

/-- Stage one has empty earlier factor and two future factors. -/
def firstEquiv : ((K ⊗[K] F) ⊗[K] (F ⊗[K] F)) ≃ₗ[K] Ambient K F :=
  TensorProduct.congr (TensorProduct.lid K F) (LinearEquiv.refl K (F ⊗[K] F))

/-- Stage two has one earlier and one future factor. -/
def secondEquiv : ((F ⊗[K] F) ⊗[K] F) ≃ₗ[K] Ambient K F := TensorProduct.assoc K F F F

/-- Stage three has two earlier factors and the empty future factor. -/
def thirdEquiv : (((F ⊗[K] F) ⊗[K] F) ⊗[K] K) ≃ₗ[K] Ambient K F :=
  (TensorProduct.rid K ((F ⊗[K] F) ⊗[K] F)).trans secondEquiv

theorem first_pairing (B : LinearMap.BilinForm K F)
    (x y : (K ⊗[K] F) ⊗[K] (F ⊗[K] F)) :
    form B (form B B) (firstEquiv x) (firstEquiv y) =
      form (form unitForm B) (form B B) x y :=
  congr_pairing _ _ _ _ _ _ (lid_pairing B) (fun _ _ => rfl) x y

theorem second_pairing (B : LinearMap.BilinForm K F) (x y : (F ⊗[K] F) ⊗[K] F) :
    form B (form B B) (secondEquiv x) (secondEquiv y) = form (form B B) B x y :=
  assoc_pairing B B B x y

theorem third_pairing (B : LinearMap.BilinForm K F)
    (x y : ((F ⊗[K] F) ⊗[K] F) ⊗[K] K) :
    form B (form B B) (thirdEquiv x) (thirdEquiv y) =
      form (form (form B B) B) unitForm x y := by
  change form B (form B B) (secondEquiv ((TensorProduct.rid K _) x))
    (secondEquiv ((TensorProduct.rid K _) y)) = _
  rw [second_pairing, rid_pairing]

/-- Concrete stage-one transport, with arbitrary current and future labels. -/
theorem first_space (V : Submodule K F) (W : Submodule K (F ⊗[K] F)) :
    (space (space (⊤ : Submodule K K) V) W).map firstEquiv.toLinearMap = space V W := by
  rw [firstEquiv, space_congr, space_lid]
  simp

/-- Concrete stage-three transport, with arbitrary earlier and current labels. -/
theorem third_space (U : Submodule K (F ⊗[K] F)) (V : Submodule K F) :
    (space (space U V) (⊤ : Submodule K K)).map thirdEquiv.toLinearMap =
      (space U V).map secondEquiv.toLinearMap := by
  change (space (space U V) ⊤).map
    (secondEquiv.toLinearMap.comp (TensorProduct.rid K _).toLinearMap) = _
  rw [Submodule.map_comp, space_rid]

/-- Stage-one source is the actual three-factor terminal line. -/
theorem x_source (t₁ t₂ t₃ : F) :
    (space (space (⊤ : Submodule K K) (K ∙ t₁)) (K ∙ (t₂ ⊗ₜ[K] t₃))).map
      firstEquiv.toLinearMap = K ∙ (t₁ ⊗ₜ[K] (t₂ ⊗ₜ[K] t₃)) := by
  rw [first_space, space_lines]

/-- Exposing the first factor agrees exactly with the next stage's X input. -/
theorem x_interstage_one_two (t₂ t₃ : F) :
    (space (space (⊤ : Submodule K K) (⊤ : Submodule K F)) (K ∙ (t₂ ⊗ₜ[K] t₃))).map
      firstEquiv.toLinearMap =
    (space (space (⊤ : Submodule K F) (K ∙ t₂)) (K ∙ t₃)).map secondEquiv.toLinearMap := by
  rw [first_space]
  change _ = (space (space ⊤ (K ∙ t₂)) (K ∙ t₃)).map (TensorProduct.assoc K F F F).toLinearMap
  rw [space_assoc, space_lines]

/-- Exposing the second factor agrees exactly with stage three's X input. -/
theorem x_interstage_two_three (t₃ : F) :
    (space (space (⊤ : Submodule K F) (⊤ : Submodule K F)) (K ∙ t₃)).map secondEquiv.toLinearMap =
    (space (space (⊤ : Submodule K (F ⊗[K] F)) (K ∙ t₃)) (⊤ : Submodule K K)).map
      thirdEquiv.toLinearMap := by
  rw [third_space, top_top]

/-- The final X stage reaches the whole cube ambient. -/
theorem x_sink :
    (space (space (⊤ : Submodule K (F ⊗[K] F)) (⊤ : Submodule K F))
      (⊤ : Submodule K K)).map thirdEquiv.toLinearMap = (⊤ : Submodule K (Ambient K F)) := by
  rw [third_space, top_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (secondEquiv (K := K) (F := F)).surjective

/-- Stage-one Y starts at zero, as its earlier complement is actually zero. -/
theorem y_source (t₁ t₂ t₃ : F) :
    (space (space ((unitForm : LinearMap.BilinForm K K).orthogonal (K ∙ (1 : K))) (K ∙ t₁))
      (K ∙ (t₂ ⊗ₜ[K] t₃))).map firstEquiv.toLinearMap = ⊥ := by
  rw [scalar_line_one, unit_orthogonal_top, space_bot_left, space_bot_left, Submodule.map_bot]

/-- The actual first Y output equals the next stage's orthogonal-prefix input. -/
theorem y_interstage_one_two (B : LinearMap.BilinForm K F) (t₁ t₂ t₃ : F) :
    (space ((form unitForm B).orthogonal (space (K ∙ (1 : K)) (K ∙ t₁)))
      (K ∙ (t₂ ⊗ₜ[K] t₃))).map firstEquiv.toLinearMap =
    (space (space (B.orthogonal (K ∙ t₁)) (K ∙ t₂)) (K ∙ t₃)).map secondEquiv.toLinearMap := by
  rw [firstEquiv, space_congr, map_orthogonal _ _ _ (lid_pairing B), scalar_line_one, space_lid]
  simp only [LinearEquiv.refl_toLinearMap, Submodule.map_id]
  change _ = (space (space (B.orthogonal (K ∙ t₁)) (K ∙ t₂)) (K ∙ t₃)).map
    (TensorProduct.assoc K F F F).toLinearMap
  rw [space_assoc, space_lines]

/-- The exposed two-factor tensor line gives the exact third-stage earlier complement. -/
theorem y_interstage_two_three (B : LinearMap.BilinForm K F) (t₁ t₂ t₃ : F) :
    (space ((form B B).orthogonal (space (K ∙ t₁) (K ∙ t₂))) (K ∙ t₃)).map secondEquiv.toLinearMap =
    (space (space ((form B B).orthogonal (K ∙ (t₁ ⊗ₜ[K] t₂))) (K ∙ t₃))
      (⊤ : Submodule K K)).map thirdEquiv.toLinearMap := by
  rw [third_space, space_lines]

/-- The last Y label is precisely the actual orthogonal complement of the terminal cube line. -/
theorem y_sink (B : LinearMap.BilinForm K F) (t₁ t₂ t₃ : F) :
    (space ((form (form B B) B).orthogonal (space (K ∙ (t₁ ⊗ₜ[K] t₂)) (K ∙ t₃)))
      (⊤ : Submodule K K)).map thirdEquiv.toLinearMap =
    (form B (form B B)).orthogonal (K ∙ (t₁ ⊗ₜ[K] (t₂ ⊗ₜ[K] t₃))) := by
  change (space ((form (form B B) B).orthogonal (space (K ∙ (t₁ ⊗ₜ[K] t₂)) (K ∙ t₃))) ⊤).map
    (secondEquiv.toLinearMap.comp (TensorProduct.rid K _).toLinearMap) = _
  rw [Submodule.map_comp, space_rid, map_orthogonal _ _ _ (second_pairing B), space_lines]
  congr 1
  simp [Submodule.map_span, secondEquiv]

section Geometries
variable [FiniteDimensional K F]

/-- The empty prefix carries the ordinary scalar multiplication pairing. -/
theorem unit_nondegenerate : (unitForm : LinearMap.BilinForm K K).Nondegenerate := by
  constructor
  · intro x hx
    simpa [unitForm] using hx 1
  · intro x hx
    simpa [unitForm] using hx 1

theorem unit_symm : (unitForm : LinearMap.BilinForm K K).IsSymm := by
  exact ⟨fun x y => mul_comm x y⟩

/-- Stage one uses the scalar empty prefix and its distinguished vector one. -/
def firstGeometry (B : LinearMap.BilinForm K F) (hs : B.IsSymm) (hn : B.Nondegenerate) :
    MotifLabels.Geometry K K F where
  earlier := unitForm
  current := B
  earlier_symm := unit_symm
  current_symm := hs
  earlier_nd := unit_nondegenerate
  current_nd := hn
  p := 1
  p_norm := by simp [unitForm]

/-- Stage two uses the first terminal vector as its distinguished prefix. -/
def secondGeometry (B : LinearMap.BilinForm K F) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (t₁ : F) (ht₁ : B t₁ t₁ ≠ 0) : MotifLabels.Geometry K F F where
  earlier := B
  current := B
  earlier_symm := hs
  current_symm := hs
  earlier_nd := hn
  current_nd := hn
  p := t₁
  p_norm := ht₁

/-- Stage three uses the actual tensor of the first two terminal vectors. -/
def thirdGeometry (B : LinearMap.BilinForm K F) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (t₁ t₂ : F) (ht₁ : B t₁ t₁ ≠ 0) (ht₂ : B t₂ t₂ ≠ 0) :
    MotifLabels.Geometry K (F ⊗[K] F) F where
  earlier := form B B
  current := B
  earlier_symm := LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp hs).tmul (LinearMap.BilinForm.isSymm_iff.mp hs))
  current_symm := hs
  earlier_nd := Labels.tmul_nondegenerate B B hn hn
  current_nd := hn
  p := t₁ ⊗ₜ[K] t₂
  p_norm := by simpa only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using mul_ne_zero ht₂ ht₁

open MotifLabels.Geometry

omit [FiniteDimensional K F] in
/-- Stage-one local X inputs transport to the prescribed terminal lines. -/
theorem geometry_x_source (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) :
    (liftLabel (t₂ ⊗ₜ[K] t₃) ((firstGeometry B hs hn).xIn t₁)).map firstEquiv.toLinearMap =
      K ∙ (t₁ ⊗ₜ[K] (t₂ ⊗ₜ[K] t₃)) := x_source t₁ t₂ t₃

omit [FiniteDimensional K F] in
/-- Stage-one local Y inputs transport to zero. -/
theorem geometry_y_source (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) :
    (liftLabel (t₂ ⊗ₜ[K] t₃) ((firstGeometry B hs hn).yIn t₁)).map firstEquiv.toLinearMap =
      ⊥ := y_source t₁ t₂ t₃

omit [FiniteDimensional K F] in
/-- Actual local X labels match between stages one and two. -/
theorem geometry_x_one_two (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) (ht₁ : B t₁ t₁ ≠ 0) :
    (liftLabel (t₂ ⊗ₜ[K] t₃) (firstGeometry B hs hn).full).map firstEquiv.toLinearMap =
    (liftLabel t₃ ((secondGeometry B hs hn t₁ ht₁).xIn t₂)).map secondEquiv.toLinearMap :=
  x_interstage_one_two t₂ t₃

/-- Actual local X labels match between stages two and three. -/
theorem geometry_x_two_three (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) (ht₁ : B t₁ t₁ ≠ 0) (ht₂ : B t₂ t₂ ≠ 0) :
    (liftLabel t₃ (secondGeometry B hs hn t₁ ht₁).full).map secondEquiv.toLinearMap =
    (liftLabel (1 : K) ((thirdGeometry B hs hn t₁ t₂ ht₁ ht₂).xIn t₃)).map
      thirdEquiv.toLinearMap := by
  change (space (space (⊤ : Submodule K F) (⊤ : Submodule K F)) (K ∙ t₃)).map
    secondEquiv.toLinearMap = (space (space (⊤ : Submodule K (F ⊗[K] F)) (K ∙ t₃))
      (K ∙ (1 : K))).map thirdEquiv.toLinearMap
  rw [scalar_line_one]
  exact x_interstage_two_three t₃

/-- Actual local X output at stage three is the whole cube. -/
theorem geometry_x_sink (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ : F) (ht₁ : B t₁ t₁ ≠ 0) (ht₂ : B t₂ t₂ ≠ 0) :
    (liftLabel (1 : K) (thirdGeometry B hs hn t₁ t₂ ht₁ ht₂).full).map
      thirdEquiv.toLinearMap = ⊤ := by
  change (space (space (⊤ : Submodule K (F ⊗[K] F)) (⊤ : Submodule K F))
    (K ∙ (1 : K))).map thirdEquiv.toLinearMap = ⊤
  rw [scalar_line_one]
  exact x_sink

/-- The actual local motif Y outputs and inputs agree across the first boundary. -/
theorem geometry_y_one_two (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) (ht₁ : B t₁ t₁ ≠ 0) :
    (liftLabel (t₂ ⊗ₜ[K] t₃) ((firstGeometry B hs hn).yOut t₁)).map firstEquiv.toLinearMap =
    (liftLabel t₃ ((secondGeometry B hs hn t₁ ht₁).yIn t₂)).map secondEquiv.toLinearMap := by
  rw [(firstGeometry B hs hn).yOut_eq_orthogonal t₁ ht₁]
  exact y_interstage_one_two B t₁ t₂ t₃

/-- The actual local motif Y outputs and inputs agree across the second boundary. -/
theorem geometry_y_two_three (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) (ht₁ : B t₁ t₁ ≠ 0) (ht₂ : B t₂ t₂ ≠ 0) :
    (liftLabel t₃ ((secondGeometry B hs hn t₁ ht₁).yOut t₂)).map secondEquiv.toLinearMap =
    (liftLabel (1 : K) ((thirdGeometry B hs hn t₁ t₂ ht₁ ht₂).yIn t₃)).map
      thirdEquiv.toLinearMap := by
  rw [(secondGeometry B hs hn t₁ ht₁).yOut_eq_orthogonal t₂ ht₂]
  change (space ((form B B).orthogonal (space (K ∙ t₁) (K ∙ t₂))) (K ∙ t₃)).map
    secondEquiv.toLinearMap = (space (space ((form B B).orthogonal (K ∙ (t₁ ⊗ₜ[K] t₂)))
      (K ∙ t₃)) (K ∙ (1 : K))).map thirdEquiv.toLinearMap
  rw [scalar_line_one]
  exact y_interstage_two_three B t₁ t₂ t₃

/-- The third actual local Y output is the required cube-line complement. -/
theorem geometry_y_sink (B : LinearMap.BilinForm K F) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (t₁ t₂ t₃ : F) (ht₁ : B t₁ t₁ ≠ 0)
    (ht₂ : B t₂ t₂ ≠ 0) (ht₃ : B t₃ t₃ ≠ 0) :
    (liftLabel (1 : K) ((thirdGeometry B hs hn t₁ t₂ ht₁ ht₂).yOut t₃)).map
      thirdEquiv.toLinearMap =
    (form B (form B B)).orthogonal (K ∙ (t₁ ⊗ₜ[K] (t₂ ⊗ₜ[K] t₃))) := by
  rw [(thirdGeometry B hs hn t₁ t₂ ht₁ ht₂).yOut_eq_orthogonal t₃ ht₃]
  change (space ((form (form B B) B).orthogonal (space (K ∙ (t₁ ⊗ₜ[K] t₂)) (K ∙ t₃)))
    (K ∙ (1 : K))).map thirdEquiv.toLinearMap = _
  rw [scalar_line_one]
  exact y_sink B t₁ t₂ t₃

end Geometries

end IntegerMultBounds.Networks.StageLabels
