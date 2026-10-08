import IntegerMultBounds.Networks.TensorCoordinates
import IntegerMultBounds.Networks.BinaryPhase
import IntegerMultBounds.Networks.NeighborCounts

/-! Exact coordinate support and Hamming weight of the actual tensor terminal
vectors. The coordinate permutation is retained; cardinality is invariant
under that permutation. -/

namespace IntegerMultBounds.Networks.TensorTerminalWeight

open Module Labels TensorCoordinates
open scoped TensorProduct

variable {h : ℕ}

theorem coordinates_tmul (x y z : Fin h → ZMod 2) (i : Fin h × (Fin h × Fin h)) :
    coordinates h (x ⊗ₜ[ZMod 2] (y ⊗ₜ[ZMod 2] z)) (index h i) = x i.1 * (y i.2.1 * z i.2.2) := by
  rcases i with ⟨i, j, l⟩
  simp [coordinates, cubeBasis, Basis.equivFun_apply, productBasis, smul_eq_mul, mul_comm]

/-- The actual support is the indexed Cartesian product of the three sets. -/
theorem coordinates_cubeVector (A B C : Finset (Fin h)) (i : Fin h × (Fin h × Fin h)) :
    coordinates h (cubeVector (K := ZMod 2) A B C) (index h i) =
      if i.1 ∈ A ∧ i.2.1 ∈ B ∧ i.2.2 ∈ C then 1 else 0 := by
  rw [cubeVector, coordinates_tmul]
  simp only [indicator]
  split_ifs <;> simp_all

theorem weight_cubeVector (A B C : Finset (Fin h)) :
    BinaryPhase.weight (coordinates h (cubeVector (K := ZMod 2) A B C)) = A.card * B.card * C.card := by
  unfold BinaryPhase.weight
  rw [← (index h).sum_comp]
  simp only [coordinates_cubeVector]
  have hv (p : Prop) [Decidable p] : (if p then (1 : ZMod 2) else 0).val = if p then 1 else 0 := by
    split_ifs <;> rfl
  simp_rw [hv]
  simp [Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel, mul_assoc]

/-- Every triple tensor has twenty-seven set coordinates, regardless of the
particular triples or of the coordinate enumeration. -/
theorem weight_triples (A B C : NeighborCounts.Triple h) :
    BinaryPhase.weight (coordinates h (cubeVector (K := ZMod 2) A.val B.val C.val)) = 27 := by
  rw [weight_cubeVector, A.property, B.property, C.property]

end IntegerMultBounds.Networks.TensorTerminalWeight
