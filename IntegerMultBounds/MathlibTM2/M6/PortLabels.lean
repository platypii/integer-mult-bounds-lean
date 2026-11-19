module

public import IntegerMultBounds.MathlibTM2.M6.PortRotation
public import IntegerMultBounds.MathlibTM2.M6.PrefixLabel

/-! The port rotation reconciles the literal source and target boundary labels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589

def portLineLabel (t : Fin 111) : Fin 636 :=
  ⟨Frames.initialRefs t.val, Frames.initial_ids_bounded ⟨t.val, by omega⟩⟩

def portHyperplaneLabel (t : Fin 111) : Fin 636 :=
  ⟨Frames.finalRefs (111 + t.val), Frames.final_ids_bounded ⟨111 + t.val, by omega⟩⟩

def portFullLabel (t : Fin 111) : Fin 636 :=
  ⟨Frames.finalRefs t.val, Frames.final_ids_bounded ⟨t.val, by omega⟩⟩

def portEmptyLabel (t : Fin 111) : Fin 636 :=
  ⟨Frames.initialRefs (111 + t.val), Frames.initial_ids_bounded ⟨111 + t.val, by omega⟩⟩

private theorem port_dimensions : ∀ t : Fin 111,
    Geometry.Dimensions.value (portLineLabel t).val = 1 ∧
    Geometry.Dimensions.value (portHyperplaneLabel t).val = 7 := by decide +kernel

/-- Every port of the literal word uses the same cyclic permutation. Only the
two triangular factors depend on the port and the coefficient ring. -/
theorem port_label_routes {R : Type*} [CommRing R] (P : Fin 636 → Matrix (Fin 8) (Fin 8) R)
    (lower : ∀ l i j, i < j → P l i j = 0)
    (diag : ∀ l (i : Fin 8), P l i i = if i.val < Geometry.Dimensions.value l.val then 1 else 0)
    (idem : ∀ l, P l * P l = P l) (t : Fin 111) :
    ∃ A B : Matrix (Fin 8) (Fin 8) R, A.IsLowerTriangular ∧ B.IsLowerTriangular ∧
      IsUnit A ∧ IsUnit B ∧ (B * portRotation * A) * (1 - P (portLineLabel t)) =
        P (portHyperplaneLabel t) * (B * portRotation * A) := by
  apply port_complement_route (P (portLineLabel t)) (P (portHyperplaneLabel t)) (fun {_ _} h => lower _ _ _ h)
    (fun {_ _} h => lower _ _ _ h) (idem _) (idem _)
  · intro i
    rw [diag, (port_dimensions t).1]
  · intro i
    rw [diag, (port_dimensions t).2]

/-- The other two endpoint labels are exactly the identity and zero projectors
over every modular radix, including the trivial ring. -/
theorem port_full_empty {R : Type*} [CommRing R] (P : Fin 636 → Matrix (Fin 8) (Fin 8) R)
    (lower : ∀ l i j, i < j → P l i j = 0)
    (diag : ∀ l (i : Fin 8), P l i i = if i.val < Geometry.Dimensions.value l.val then 1 else 0)
    (idem : ∀ l, P l * P l = P l) (t : Fin 111) :
    P (portFullLabel t) = 1 ∧ P (portEmptyLabel t) = 0 := by
  have dims : ∀ t : Fin 111, Geometry.Dimensions.value (portFullLabel t).val = 8 ∧
      Geometry.Dimensions.value (portEmptyLabel t).val = 0 := by decide +kernel
  have full (A : Matrix (Fin 8) (Fin 8) R) (tri : A.IsLowerTriangular)
      (ones : ∀ i, A i i = 1) (square : A * A = A) : A = 1 := by
    have unit : IsUnit A.det := by simp [A.det_of_isLowerTriangular tri, ones]
    have h := congrArg (fun M => A⁻¹ * M) square
    simpa only [← Matrix.mul_assoc, A.nonsing_inv_mul unit, Matrix.one_mul] using h
  constructor
  · exact full _ (fun {_ _} h => lower _ _ _ h)
      (fun i => by rw [diag, (dims t).1, ite_eq_left i.isLt]) (idem _)
  · let A := P (portEmptyLabel t)
    have tri : (1 - A).IsLowerTriangular := by
      intro i j h
      have lt : i < j := h
      simp [A, Matrix.sub_apply, one_apply_ne lt.ne, lower _ _ _ lt]
    have ones (i : Fin 8) : (1 - A) i i = 1 := by simp [A, diag, (dims t).2]
    have square : (1 - A) * (1 - A) = 1 - A := by
      rw [sub_mul, one_mul, mul_sub, mul_one, show A * A = A from idem _, sub_self, sub_zero]
    exact sub_eq_self.mp (full _ tri ones square)

end IntegerMultBounds.MathlibTM2.M6
