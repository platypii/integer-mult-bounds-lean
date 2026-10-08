import IntegerMultBounds.Networks.Labels
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Tensor label spaces for the three-coordinate motifs. Nondegeneracy is
proved from the Kronecker matrix of the tensor form, over either label field.
These are actual tensor spaces, not an assumed dimension or rank interface. -/

namespace IntegerMultBounds.Networks.Labels

open scoped TensorProduct Kronecker
open Module

section Tensor
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]

/-- Tensoring finite nondegenerate forms preserves nondegeneracy, including
over characteristic two; no positive-definiteness assumption is used. -/
theorem tmul_nondegenerate (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) : (B.tmul C).Nondegenerate := by
  classical
  let b := Module.finBasis K E
  let c := Module.finBasis K F
  have hm : LinearMap.BilinForm.toMatrix (b.tensorProduct c) (B.tmul C) =
      (LinearMap.BilinForm.toMatrix b B) ⊗ₖ (LinearMap.BilinForm.toMatrix c C) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Module.Basis.tensorProduct_apply',
      LinearMap.BilinForm.tmul, smul_eq_mul, mul_comm]
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (B.tmul C) (b.tensorProduct c)
  rw [hm, Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB))
    (pow_ne_zero _ ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp hC))

end Tensor

abbrev Cube (K : Type*) [CommRing K] (h : ℕ) :=
  (Fin h → K) ⊗[K] ((Fin h → K) ⊗[K] (Fin h → K))

def cubeForm {K : Type*} [CommRing K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) : LinearMap.BilinForm K (Cube K h) :=
  B.tmul (B.tmul B)

def cubeVector {K : Type*} [CommRing K] {h : ℕ}
    (S T U : Finset (Fin h)) : Cube K h :=
  indicator S ⊗ₜ[K] (indicator T ⊗ₜ[K] indicator U)

theorem cube_pairing {K : Type*} [CommRing K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (S T U S' T' U' : Finset (Fin h)) :
    cubeForm B (cubeVector S T U) (cubeVector S' T' U') =
      B (indicator S) (indicator S') * B (indicator T) (indicator T') *
        B (indicator U) (indicator U') := by
  simp only [cubeForm, cubeVector, LinearMap.BilinForm.tmul,
    LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
  ring

theorem cube_nondegenerate {K : Type*} [Field K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (hB : B.Nondegenerate) :
    (cubeForm B).Nondegenerate := tmul_nondegenerate B _ hB (tmul_nondegenerate B B hB hB)

theorem cube_finrank {K : Type*} [Field K] (h : ℕ) :
    Module.finrank K (Cube K h) = h ^ 3 := by
  simp [Cube, Module.finrank_tensorProduct, pow_succ]
  ring

theorem rational_cube_nondegenerate {h : ℕ} (hh : h ≠ 9) :
    (cubeForm (rational h)).Nondegenerate := cube_nondegenerate _ (rational_nondegenerate hh)

theorem binary_cube_nondegenerate (h : ℕ) :
    (cubeForm (binary h)).Nondegenerate := cube_nondegenerate _ binary_nondegenerate

theorem rational_cube_self {h : ℕ} (S T U : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hu : U.card = 3) :
    cubeForm (rational h) (cubeVector S T U) (cubeVector S T U) = 8 := by
  rw [cube_pairing, rational_self S hs, rational_self T ht, rational_self U hu]
  norm_num

theorem binary_cube_self {h : ℕ} (S T U : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hu : U.card = 3) :
    cubeForm (binary h) (cubeVector S T U) (cubeVector S T U) = 1 := by
  rw [cube_pairing, binary_self S hs, binary_self T ht, binary_self U hu]
  simp

theorem rational_cube_line_nondegenerate {h : ℕ} (S T U : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hu : U.card = 3) :
    ((cubeForm (rational h)).restrict (Submodule.span ℚ {cubeVector S T U})).Nondegenerate := by
  apply line_nondegenerate
  rw [rational_cube_self S T U hs ht hu]
  norm_num

theorem binary_cube_line_nondegenerate {h : ℕ} (S T U : Finset (Fin h))
    (hs : S.card = 3) (ht : T.card = 3) (hu : U.card = 3) :
    ((cubeForm (binary h)).restrict
      (Submodule.span (ZMod 2) {cubeVector S T U})).Nondegenerate := by
  apply line_nondegenerate
  rw [binary_cube_self S T U hs ht hu]
  exact one_ne_zero

theorem cube_symm {K : Type*} [CommRing K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (hs : B.IsSymm) : (cubeForm B).IsSymm := by
  have hs' := LinearMap.BilinForm.isSymm_iff.mp hs
  exact LinearMap.BilinForm.isSymm_iff.mpr (hs'.tmul (hs'.tmul hs'))

/-- The terminal line and its orthogonal complement have exactly the dimensions
used in the network budget, with a genuine nondegenerate direct decomposition. -/
theorem cube_line_decomposition {K : Type*} [Field K] {h : ℕ}
    (B : LinearMap.BilinForm K (Fin h → K)) (hn : B.Nondegenerate) (hs : B.IsSymm)
    (S T U : Finset (Fin h))
    (hv : cubeForm B (cubeVector S T U) (cubeVector S T U) ≠ 0) :
    let L := Submodule.span K {cubeVector (K := K) S T U}
    IsCompl L ((cubeForm B).orthogonal L) ∧
      Module.finrank K L = 1 ∧
      Module.finrank K ((cubeForm B).orthogonal L) = h ^ 3 - 1 ∧
      ((cubeForm B).restrict ((cubeForm B).orthogonal L)).Nondegenerate := by
  dsimp only
  have hvec : cubeVector (K := K) S T U ≠ 0 := by
    intro hz
    apply hv
    simp [hz]
  have hdim := finrank_span_singleton (K := K) hvec
  refine ⟨LinearMap.BilinForm.isCompl_span_singleton_orthogonal hv, hdim, ?_, ?_⟩
  · rw [LinearMap.BilinForm.finrank_orthogonal (cube_nondegenerate B hn), cube_finrank, hdim]
  · exact LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
      (cubeForm B) (cube_nondegenerate B hn) (cube_symm B hs).isRefl hv

end IntegerMultBounds.Networks.Labels
