import IntegerMultBounds.Networks.TensorLabels
import Mathlib.Data.Fintype.EquivFin

/-! The binary tensor cube is identified with its actual coordinate-bit space.
This bridges tensor-subspace labels and the Hamming-weight phase interface. -/

namespace IntegerMultBounds.Networks.TensorCoordinates

open Module Labels
open scoped TensorProduct

section General
variable {K E F ι κ : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [DecidableEq ι] [DecidableEq κ]

theorem tensor_gram (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (b : Basis ι K E) (c : Basis κ K F)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (hc : ∀ i j, C (c i) (c j) = if i = j then 1 else 0) (i j : ι × κ) :
    B.tmul C (b.tensorProduct c i) (b.tensorProduct c j) = if i = j then 1 else 0 := by
  simp only [Basis.tensorProduct_apply', LinearMap.BilinForm.tmul,
    LinearMap.BilinForm.tensorDistrib_tmul, hb, hc, smul_eq_mul]
  by_cases hi : i.1 = j.1 <;> by_cases hj : i.2 = j.2 <;>
    simp [hi, hj, Prod.ext_iff]

/-- In an orthonormal basis the bilinear form is the literal coordinate dot
product on every vector, not merely on the basis elements. -/
theorem coordinates_pairing [Fintype ι] (B : LinearMap.BilinForm K E)
    (b : Basis ι K E) (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (x y : E) :
    B x y = ∑ i, b.equivFun x i * b.equivFun y i := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hb, Basis.equivFun_apply]
  simp [mul_comm]

end General

noncomputable def productBasis (h : ℕ) :
    Basis (Fin h × (Fin h × Fin h)) (ZMod 2) (Cube (ZMod 2) h) :=
  (Pi.basisFun (ZMod 2) (Fin h)).tensorProduct
    ((Pi.basisFun (ZMod 2) (Fin h)).tensorProduct (Pi.basisFun (ZMod 2) (Fin h)))

theorem coordinate_gram (h : ℕ) (i j : Fin h) :
    binary h (Pi.basisFun (ZMod 2) (Fin h) i) (Pi.basisFun (ZMod 2) (Fin h) j) =
      if i = j then 1 else 0 := by
  simp [Pi.basisFun_apply, binary, form_single, Pi.single_apply, eq_comm]

theorem productBasis_gram (h : ℕ) (i j : Fin h × (Fin h × Fin h)) :
    cubeForm (binary h) (productBasis h i) (productBasis h j) = if i = j then 1 else 0 := by
  exact tensor_gram _ _ _ _ (coordinate_gram h)
    (tensor_gram _ _ _ _ (coordinate_gram h) (coordinate_gram h)) i j

noncomputable def index (h : ℕ) : (Fin h × (Fin h × Fin h)) ≃ Fin (h ^ 3) :=
  Fintype.equivFinOfCardEq (by simp [pow_succ]; ring)

noncomputable def cubeBasis (h : ℕ) : Basis (Fin (h ^ 3)) (ZMod 2) (Cube (ZMod 2) h) :=
  (productBasis h).reindex (index h)

theorem cubeBasis_gram (h : ℕ) (i j : Fin (h ^ 3)) :
    cubeForm (binary h) (cubeBasis h i) (cubeBasis h j) = if i = j then 1 else 0 := by
  simp only [cubeBasis, Basis.reindex_apply, productBasis_gram, (index h).symm.injective.eq_iff]

/-- Exact binary coordinates, with exactly h cubed bits. -/
noncomputable def coordinates (h : ℕ) : Cube (ZMod 2) h ≃ₗ[ZMod 2] (Fin (h ^ 3) → ZMod 2) :=
  (cubeBasis h).equivFun

theorem coordinates_isometry (h : ℕ) (x y : Cube (ZMod 2) h) :
    binary (h ^ 3) (coordinates h x) (coordinates h y) = cubeForm (binary h) x y := by
  rw [coordinates_pairing _ (cubeBasis h) (cubeBasis_gram h)]
  simp [binary, form_apply, coordinates]

end IntegerMultBounds.Networks.TensorCoordinates
