module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame

/-! Reconciling the complement of a prefix line with a prefix hyperplane at a port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589.Nine

/-- The cyclic coordinate shift moves the seven trailing positions to the seven leading ones. -/
def portRotation {R : Type*} [CommRing R] : Matrix (Fin 8) (Fin 8) R :=
  of fun i j => if j = i + 1 then 1 else 0

theorem portRotation_isUnit {R : Type*} [CommRing R] : IsUnit (portRotation (R := R)) := by
  have inverse : (portRotation : Matrix (Fin 8) (Fin 8) R) * portRotationᵀ = 1 := by
    ext i j
    simp [Matrix.mul_apply, portRotation, Matrix.one_apply, eq_comm]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse inverse)

private theorem rotate_complement {R : Type*} [CommRing R] :
    let L : Matrix (Fin 8) (Fin 8) R := diagonal fun i => if i.val < 1 then 1 else 0
    let H : Matrix (Fin 8) (Fin 8) R := diagonal fun i => if i.val < 7 then 1 else 0
    portRotation * (1 - L) = H * portRotation := by
  intro L H
  ext i j
  simp only [L, H, mul_sub, mul_one, Matrix.sub_apply, mul_diagonal, diagonal_mul, portRotation, of_apply]
  have h : ∀ k : Fin 8, (k + 1).val < 1 ↔ ¬ k.val < 7 := by decide
  by_cases eq : j = i + 1
  · subst j
    by_cases hi : i.val < 7 <;> simp [h, hi]
  · simp [eq]

/-- For any modular line and hyperplane with the certified prefix pivots, triangular
basis changes on either side of the same cyclic shift reconcile the two port frames. -/
theorem port_complement_route {R : Type*} [CommRing R] (L H : Matrix (Fin 8) (Fin 8) R)
    (ltL : L.IsLowerTriangular) (ltH : H.IsLowerTriangular)
    (idemL : L * L = L) (idemH : H * H = H)
    (line : ∀ i : Fin 8, L i i = if i.val < 1 then 1 else 0)
    (hyper : ∀ i : Fin 8, H i i = if i.val < 7 then 1 else 0) :
    ∃ A B : Matrix (Fin 8) (Fin 8) R, A.IsLowerTriangular ∧ B.IsLowerTriangular ∧
      IsUnit A ∧ IsUnit B ∧ (B * portRotation * A) * (1 - L) = H * (B * portRotation * A) := by
  obtain ⟨C, tri, _, unit, lc⟩ := triangular_projector_basis L ltL idemL
    (fun i => by rw [line]; split <;> simp)
  obtain ⟨B, tb, _, ub, hb⟩ := triangular_projector_basis H ltH idemH
    (fun i => by rw [hyper]; split <;> simp)
  let := C.invertibleOfIsUnitDet unit
  rw [funext line] at lc
  rw [funext hyper] at hb
  have inv := C.mul_nonsing_inv unit
  have inv' := C.nonsing_inv_mul unit
  have il := congrArg (fun M => C⁻¹ * M * C⁻¹) lc
  simp only [← Matrix.mul_assoc, inv', Matrix.one_mul] at il
  rw [Matrix.mul_assoc (C⁻¹ * L), inv, Matrix.mul_one] at il
  refine ⟨C⁻¹, B, blockTriangular_inv_of_blockTriangular tri, tb,
    Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr unit),
    (Matrix.isUnit_iff_isUnit_det _).mpr ub, ?_⟩
  have complement := rotate_complement (R := R)
  simp only [mul_sub, mul_one] at complement
  simp only [mul_sub, mul_one, Matrix.mul_assoc]
  rw [← il, ← Matrix.mul_assoc portRotation, ← mul_sub, ← sub_mul, complement]
  rw [← Matrix.mul_assoc H B, ← hb]
  simp only [Matrix.mul_assoc]

end IntegerMultBounds.MathlibTM2.M6
