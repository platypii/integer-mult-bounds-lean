import IntegerMultBounds.Networks.TensorLabels
import Mathlib.RingTheory.Flat.Basic

/-! Tensor products of labels as actual subspaces of the ambient tensor space.
These constructions retain inclusion, dimensions, nondegeneracy, and
orthogonality, rather than recording them as annotations. -/

namespace IntegerMultBounds.Networks.TensorSubspace

open scoped TensorProduct
open Module

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]

def space (U : Submodule K E) (V : Submodule K F) : Submodule K (E ⊗[K] F) :=
  LinearMap.range (TensorProduct.mapIncl U V)

abbrev form (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F) :
    LinearMap.BilinForm K (E ⊗[K] F) := B.tmul C

theorem tmul_mem (U : Submodule K E) (V : Submodule K F)
    {u : E} {v : F} (hu : u ∈ U) (hv : v ∈ V) : u ⊗ₜ[K] v ∈ space U V :=
  ⟨(⟨u, hu⟩ : U) ⊗ₜ[K] (⟨v, hv⟩ : V), rfl⟩

theorem mono {U U' : Submodule K E} {V V' : Submodule K F} (hu : U ≤ U') (hv : V ≤ V') :
    space U V ≤ space U' V' := TensorProduct.range_mapIncl_mono hu hv

theorem sup_left (U U' : Submodule K E) (V : Submodule K F) :
    space (U ⊔ U') V = space U V ⊔ space U' V := by
  simp only [space, TensorProduct.range_mapIncl, Submodule.map₂_sup_left]

theorem sup_right (U : Submodule K E) (V V' : Submodule K F) :
    space U (V ⊔ V') = space U V ⊔ space U V' := by
  simp only [space, TensorProduct.range_mapIncl, Submodule.map₂_sup_right]

theorem top_top : space (⊤ : Submodule K E) (⊤ : Submodule K F) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul u v => exact tmul_mem _ _ (Submodule.mem_top) (Submodule.mem_top)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem finrank_space [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (V : Submodule K F) :
    finrank K (space U V) = finrank K U * finrank K V := by
  rw [space, LinearMap.finrank_range_of_inj
    (Module.Flat.tensorProduct_mapIncl_injective_of_right U V), finrank_tensorProduct]

theorem pairing (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (U : Submodule K E) (V : Submodule K F) (x y : U ⊗[K] V) :
    B.tmul C (TensorProduct.mapIncl U V x) (TensorProduct.mapIncl U V y) =
      (B.restrict U).tmul (C.restrict V) x y := by
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    induction y using TensorProduct.inductionOn with
    | tmul u' v' => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Nondegeneracy passes to the embedded tensor label through its actual
inclusion map and the tensor bilinear pairing. -/
theorem nondegenerate [FiniteDimensional K E] [FiniteDimensional K F]
    (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (U : Submodule K E) (V : Submodule K F)
    (hu : (B.restrict U).Nondegenerate) (hv : (C.restrict V).Nondegenerate) :
    ((form B C).restrict (space U V)).Nondegenerate := by
  have hn := Labels.tmul_nondegenerate _ _ hu hv
  constructor
  · rintro ⟨x, ⟨x', rfl⟩⟩ hx
    have hz : x' = 0 := hn.1 x' (fun y => by
      rw [← pairing B C U V]
      exact hx ⟨_, ⟨y, rfl⟩⟩)
    apply Subtype.ext
    simp [hz]
  · rintro ⟨x, ⟨x', rfl⟩⟩ hx
    have hz : x' = 0 := hn.2 x' (fun y => by
      rw [← pairing B C U V]
      exact hx ⟨_, ⟨y, rfl⟩⟩)
    apply Subtype.ext
    simp [hz]

theorem orthogonal_left (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    {U U' : Submodule K E} (V V' : Submodule K F) (hu : U ≤ B.orthogonal U') :
    space U V ≤ (form B C).orthogonal (space U' V') := by
  rintro x ⟨x', rfl⟩ y ⟨y', rfl⟩
  induction x' using TensorProduct.inductionOn with
  | tmul u v =>
    induction y' using TensorProduct.inductionOn with
    | tmul u' v' =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.subtype_apply,
        LinearMap.BilinForm.tensorDistrib_tmul,
        hu u.property u' u'.property, smul_zero]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem orthogonal_right (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (U U' : Submodule K E) {V V' : Submodule K F} (hv : V ≤ C.orthogonal V') :
    space U V ≤ (form B C).orthogonal (space U' V') := by
  rintro x ⟨x', rfl⟩ y ⟨y', rfl⟩
  induction x' using TensorProduct.inductionOn with
  | tmul u v =>
    induction y' using TensorProduct.inductionOn with
    | tmul u' v' =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.subtype_apply,
        LinearMap.BilinForm.tensorDistrib_tmul,
        hv v.property v' v'.property, zero_smul]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end IntegerMultBounds.Networks.TensorSubspace
