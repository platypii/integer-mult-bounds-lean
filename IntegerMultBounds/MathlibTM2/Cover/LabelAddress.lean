module

public import IntegerMultBounds.Machine.FlatCoordinateLayout
public import IntegerMultBounds.MathlibTM2.Cover.Route

/-! Column-major addresses of the cover label box. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelAddress

open IntegerMultBounds.Machine.FlatCoordinateLayout

open IntegerMultBounds.MathlibTM2.M8.AtomOps
open IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Cover.Route

variable {m Q : ℕ} [NeZero Q]

/-- Pack the matrix as consecutive columns, each containing its rows in order. -/
noncomputable def address (g : Matrix (Fin m) (Fin m) (ZMod Q)) : Fin (Q ^ (m * m)) :=
  rank (refine (cols g))

/-- The base-`Q` digit at column `j`, row `i` is the matrix entry used by the route. -/
theorem entry (g : Matrix (Fin m) (Fin m) (ZMod Q)) (i j : Fin m) :
    (address g).val / Q ^ suffixFields (finProdFinEquiv (j, i)) % Q = (g i j).val := by
  have h := coordinate_value (refine (cols g)) («at» j i)
  rw [refine_at] at h
  exact h

/-- Expand each column operation over the rows present on the tape. -/
noncomputable def rowPass {R : Type*} [CommRing R] (k : ℕ) (E : Matrix (Fin m) (Fin m) R) :=
  ((OrderedAffine.program E).map atomOp).flatMap (refined (f := k))

/-- One scalar operation per row for each column operation in the ordered pass. -/
noncomputable def pass {R : Type*} [CommRing R] (E : Matrix (Fin m) (Fin m) R) :=
  rowPass m E

/-- A single rational instruction list serves every atom width. Specializing its
coefficients preserves all control and target positions, including their row indices. -/
theorem rowPass_map (k : ℕ) {R S : Type*} [CommRing R] [CommRing S] (f : R → S)
    (E : Matrix (Fin m) (Fin m) R) :
    rowPass k (E.map f) = (rowPass k E).map (OrderedAffine.mapOp f) := by
  simp only [rowPass, OrderedAffine.program_map, List.map_flatMap, List.map_map, List.flatMap_map]
  congr 1
  funext op
  cases op <;> simp [Function.comp_def, atomOp, refined, levels, OrderedAffine.mapOp]

theorem pass_map {R S : Type*} [CommRing R] [CommRing S] (f : R → S)
    (E : Matrix (Fin m) (Fin m) R) :
    pass (E.map f) = (pass E).map (OrderedAffine.mapOp f) := rowPass_map m f E

omit [NeZero Q] in
theorem pass_legal {E : Matrix (Fin m) (Fin m) (ZMod Q)}
    (h : ∀ op ∈ OrderedAffine.program E, OrderedAffine.Legal op) :
    ∀ op ∈ pass E, OrderedAffine.Legal op := by
  intro op hop
  obtain ⟨a, ha, hop⟩ := List.mem_flatMap.mp hop
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
  exact refined_legal _ (atomOp_legal (h o ho)).1 _ hop

omit [NeZero Q] in
theorem rowPass_run {k : ℕ} {E : Matrix (Fin m) (Fin m) (ZMod Q)}
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (h : ∀ op ∈ OrderedAffine.program E, OrderedAffine.Legal op)
    (g : Matrix (Fin k) (Fin m) (ZMod Q)) :
    OrderedAffine.run (rowPass k E) (refine (fun j i => g i j)) =
      refine (fun j i => (g * E.transpose) i j) := by
  unfold rowPass
  rw [refined_atomRun]
  · apply congrArg refine
    funext j i
    have eq := congrFun (atomRun_level (OrderedAffine.program E) (fun j i => g i j) i) j
    rw [OrderedAffine.program_run hE] at eq
    exact eq.trans (by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm])
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    exact (atomOp_legal (h o ho)).2

omit [NeZero Q] in
theorem pass_run {E : Matrix (Fin m) (Fin m) (ZMod Q)}
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (h : ∀ op ∈ OrderedAffine.program E, OrderedAffine.Legal op)
    (g : Matrix (Fin m) (Fin m) (ZMod Q)) :
    OrderedAffine.run (pass E) (refine (cols g)) = refine (cols (g * E.transpose)) := by
  unfold pass rowPass
  rw [refined_atomRun]
  · exact congrArg refine (lower_route hE g)
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    exact (atomOp_legal (h o ho)).2

/-- On a box with only the selected rows, the compiled scalar pass sends
each payload cell to the transformed address and preserves its suffix. -/
theorem rowPass_index {k W : ℕ} (rows : Fin k → Fin m)
    {E : Matrix (Fin m) (Fin m) (ZMod Q)}
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (h : ∀ op ∈ OrderedAffine.program E, OrderedAffine.Legal op)
    (g : Matrix (Fin m) (Fin m) (ZMod Q)) (j : Fin W) :
    (index (OrderedAffine.run (rowPass k E) (refine (fun c i => cols g c (rows i)))) j).val =
      (rank (refine (fun c i => cols (g * E.transpose) c (rows i)))).val * W + j.val := by
  unfold rowPass
  rw [refined_atomRun,index_val]
  · apply congrArg (fun x => (rank (refine x)).val * W + j.val)
    have eq := atomRun_rows (OrderedAffine.program E) rows (cols g)
    rw [lower_route hE] at eq
    exact eq
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    exact (atomOp_legal (h o ho)).2

/-- The scalar pass addresses the transformed matrix with the same trailing payload. -/
theorem pass_index {E : Matrix (Fin m) (Fin m) (ZMod Q)}
    (hE : IntegerMultBounds.Swap.Shear.LowerTriangular E)
    (h : ∀ op ∈ OrderedAffine.program E, OrderedAffine.Legal op)
    (g : Matrix (Fin m) (Fin m) (ZMod Q)) {W : ℕ} (j : Fin W) :
    (index (OrderedAffine.run (pass E) (refine (cols g))) j).val =
      (address (g * E.transpose)).val * W + j.val := by
  rw [pass_run hE h, index_val, address]

end IntegerMultBounds.MathlibTM2.Cover.LabelAddress
