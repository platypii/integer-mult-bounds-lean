import IntegerMultBounds.Swap.Shear
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Refine a lower-triangular matrix transform into a fixed finite schedule of
coordinate scalings and controlled shifts. Rows execute in descending order;
within one row, each control is earlier than its target and remains unchanged.
This reuses the existing whole-row correctness theorem and asserts no tape cost. -/

namespace IntegerMultBounds.Networks.OrderedAffine

noncomputable section
open Matrix Finset
variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

inductive Op (ι R : Type*)
  | scale (target : ι) (coefficient : R)
  | shift (target control : ι) (coefficient : R)

def execute (op : Op ι R) (x : ι → R) : ι → R :=
  match op with
  | .scale i a => Function.update x i (a * x i)
  | .shift i j a => Function.update x i (x i + a * x j)

def run (ops : List (Op ι R)) (x : ι → R) : ι → R :=
  ops.foldl (fun state op => execute op state) x

/-- Only nonrecursive §2 operations: unit target scalings and earlier controls. -/
def Legal : Op ι R → Prop
  | .scale _ a => IsUnit a
  | .shift i j _ => j < i

/-- The earlier controls can be enumerated once in any fixed order. -/
def earlier (i : ι) : List ι := (univ.filter (· < i)).toList

@[simp] theorem mem_earlier (i j : ι) : j ∈ earlier i ↔ j < i := by
  simp [earlier]

/-- One target scale, then one shift for each earlier control. -/
def row (E : Matrix ι ι R) (i : ι) : List (Op ι R) :=
  .scale i (E i i) :: (earlier i).map (fun j => .shift i j (E i j))

/-- Descending row order ensures all controls still contain their original values. -/
def program (E : Matrix ι ι R) : List (Op ι R) :=
  (Swap.Shear.descending ι).flatMap (row E)

omit [Fintype ι] in
private theorem shifts_run (i : ι) (k : ι → R) (js : List ι)
    (hne : ∀ j ∈ js, j ≠ i) (x : ι → R) :
    run (js.map (fun j => .shift i j (k j))) x =
      Function.update x i (x i + (js.map (fun j => k j * x j)).sum) := by
  induction js generalizing x with
  | nil => simp [run]
  | cons j js ih =>
    have ht : ∀ j ∈ js, j ≠ i := fun j hj => hne j (by simp [hj])
    have hu : ∀ v : R, (js.map (fun j => k j * Function.update x i v j)).sum =
        (js.map (fun j => k j * x j)).sum := by
      intro v
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [Function.update_of_ne (ht j hj)]
    change run (js.map (fun j => .shift i j (k j))) (execute (.shift i j (k j)) x) = _
    rw [ih ht]
    simp only [execute,Function.update_self,hu,Function.update_idem,List.map_cons,List.sum_cons]
    congr 1
    abel

/-- The finer schedule computes exactly the existing whole-row update. -/
theorem row_run {E : Matrix ι ι R} (hE : Swap.Shear.LowerTriangular E) (i : ι) (x : ι → R) :
    run (row E i) x = Swap.Shear.coordinateUpdate E x i := by
  have hne : ∀ j ∈ earlier i, j ≠ i := fun j hj => (mem_earlier i j |>.mp hj).ne
  have hu : ((earlier i).map (fun j => E i j * Function.update x i (E i i * x i) j)).sum =
      ((earlier i).map (fun j => E i j * x j)).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [Function.update_of_ne (hne j hj)]
  change run ((earlier i).map (fun j => .shift i j (E i j))) (execute (.scale i (E i i)) x) = _
  rw [shifts_run i (E i) _ hne]
  simp only [execute,Function.update_self,hu,Function.update_idem]
  simp only [Swap.Shear.coordinateUpdate,Swap.Shear.lower_row_apply hE,earlier,Finset.sum_map_toList]

/-- A fixed list of scalar affine operations exactly realizes matrix multiplication. -/
theorem program_run {E : Matrix ι ι R} (hE : Swap.Shear.LowerTriangular E) (x : ι → R) :
    run (program E) x = E *ᵥ x := by
  have hh : run (program E) x = Swap.Shear.orderedUpdates E (Swap.Shear.descending ι) x := by
    simp only [program,run,List.foldl_flatMap,Swap.Shear.orderedUpdates]
    congr 1
    funext state i
    exact row_run hE i state
  rw [hh,Swap.Shear.lower_transform_eq hE]

/-- Invertibility of a triangular matrix makes each diagonal scaling a unit. -/
theorem diagonal_unit {E : Matrix ι ι R} (hE : Swap.Shear.LowerTriangular E)
    (hu : IsUnit E) (i : ι) : IsUnit (E i i) := by
  have ht : E.IsLowerTriangular := fun {_ _} h => hE _ _ h
  have hd := (Matrix.isUnit_iff_isUnit_det E).mp hu
  rw [Matrix.det_of_isLowerTriangular E ht] at hd
  exact (IsUnit.prod_iff.mp hd) i (mem_univ i)

/-- An explicit inverse is sufficient; modular specialization can use the
already protected factor inverse without any new coefficient bound. -/
theorem diagonal_unit_of_inverse {E F : Matrix ι ι R}
    (hE : Swap.Shear.LowerTriangular E) (hinv : E * F = 1) (i : ι) : IsUnit (E i i) :=
  diagonal_unit hE (isUnit_iff_exists_inv.mpr ⟨F,hinv⟩) i

theorem row_legal {E : Matrix ι ι R} (hdiag : ∀ i, IsUnit (E i i)) (i : ι) :
    ∀ op ∈ row E i, Legal op := by
  intro op hop
  simp only [row,List.mem_cons,List.mem_map] at hop
  rcases hop with rfl | ⟨j,hj,rfl⟩
  · exact hdiag i
  · exact (mem_earlier i j).mp hj

/-- Every operation satisfies the ordered-affine precondition required by §2. -/
theorem program_legal {E : Matrix ι ι R} (hE : Swap.Shear.LowerTriangular E) (hu : IsUnit E) :
    ∀ op ∈ program E, Legal op := by
  intro op hop
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hop
  exact row_legal (diagonal_unit hE hu) i op hi

omit [CommRing R] in
/-- The schedule does not introduce new rational coefficients. -/
theorem coefficient_origin (E : Matrix ι ι R) (op : Op ι R) (hop : op ∈ program E) :
    (∃ i, op = .scale i (E i i)) ∨ (∃ i j, j < i ∧ op = .shift i j (E i j)) := by
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hop
  simp only [row,List.mem_cons,List.mem_map] at hi
  rcases hi with rfl | ⟨j,hj,rfl⟩
  · exact Or.inl ⟨i,rfl⟩
  · exact Or.inr ⟨i,j,(mem_earlier i j).mp hj,rfl⟩

section Specialization
variable {S : Type*}

/-- Coefficient specialization changes no target, control, or operation order. -/
def mapOp (f : R → S) : Op ι R → Op ι S
  | .scale i a => .scale i (f a)
  | .shift i j a => .shift i j (f a)

omit [CommRing R] in
/-- Even a partial-domain rational reduction can specialize the fixed schedule;
no homomorphism on all rational numbers is assumed here. -/
theorem row_map (f : R → S) (E : Matrix ι ι R) (i : ι) :
    row (E.map f) i = (row E i).map (mapOp f) := by
  simp only [row,List.map_cons,List.map_map,Function.comp_def,mapOp,Matrix.map_apply]

omit [CommRing R] in
theorem program_map (f : R → S) (E : Matrix ι ι R) :
    program (E.map f) = (program E).map (mapOp f) := by
  simp only [program,List.map_flatMap]
  congr 1
  funext i
  exact row_map f E i

end Specialization

end
end IntegerMultBounds.Networks.OrderedAffine
