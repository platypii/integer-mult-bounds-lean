module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord
public import IntegerMultBounds.MathlibTM2.Cover.Itinerary

/-! An explicit reverse schedule from the intermediate matrices of a pivot itinerary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm
variable {R : Type*} [CommRing R] {d : ℕ}

private theorem addRows_apply (k : Fin d) (rows : List (Fin d)) (hd : rows.Nodup)
    (hk : k ∉ rows) (c : Fin d → R) (x : Fin d → R) (j : Fin d) :
    (rows.flatMap (fun i => addWord k i (c i))).foldl (fun y op => op.apply y) x j =
      if j ∈ rows then x j+c j*x k else x j := by
  induction rows generalizing x with
  | nil => simp
  | cons i rows ih =>
    have ne : i ≠ k := fun e => hk (by simp [e])
    simp only [List.flatMap_cons,List.foldl_append,addWord_apply k i ne]
    rw [ih hd.tail (fun h => hk (List.mem_cons_of_mem _ h))]
    by_cases h : j = i
    · subst j; simp [hd.notMem]
    · simp [h,ne.symm]

def undoColumnWord (k pivot : Fin d) (m : Matrix (Fin d) (Fin d) R) (inv : R) : List (RowOp d R) :=
  ((List.finRange d).erase k).flatMap (fun i => addWord k i (m (Equiv.swap k pivot i) k * inv)) ++ [.swap k pivot]

theorem undoColumnWord_apply (k pivot : Fin d) (m : Matrix (Fin d) (Fin d) R) (inv : R) (x : Fin d → R) :
    (undoColumnWord k pivot m inv).foldl (fun y op => op.apply y) (stepOp k pivot m inv *ᵥ x) = x := by
  let rows := (List.finRange d).erase k
  have hd : (List.finRange d).Nodup := List.nodup_finRange d
  have mem (i : Fin d) : i ∈ rows ↔ i ≠ k := by simp [rows,hd.mem_erase_iff]
  let c := fun i => m (Equiv.swap k pivot i) k * inv
  have entry (i : Fin d) : (stepOp k pivot m inv *ᵥ x) i =
      x (Equiv.swap k pivot i) - (if i = k then 0 else c i) * x pivot := by
    rw [stepOp,← mulVec_mulVec,sub_mulVec,one_mulVec]
    change (swapMat k pivot *ᵥ x) i - (colMat k _ *ᵥ (swapMat k pivot *ᵥ x)) i = _
    simp [swapMat,colMat,mulVec,dotProduct,ite_mul,c]
  have undo (j : Fin d) := addRows_apply k rows (hd.erase _) (by simp [mem]) c (stepOp k pivot m inv *ᵥ x) j
  ext i
  simp only [undoColumnWord,List.foldl_append,List.foldl_cons,List.foldl_nil,RowOp.apply,Function.comp_apply]
  change (rows.flatMap (fun i => addWord k i (c i))).foldl (fun y op => op.apply y) (stepOp k pivot m inv *ᵥ x) (Equiv.swap k pivot i) = x i
  rw [undo]
  by_cases h : Equiv.swap k pivot i = k <;> simp [mem,entry,h]
  exact congrArg x (by simpa using (congrArg (Equiv.swap k pivot) h).symm)

noncomputable def undoItinerary (pivot : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R) :
    ℕ → List (RowOp d R)
  | 0 => []
  | n+1 =>
    let rest := undoItinerary pivot m n
    if h : n < d then
      let k : Fin d := ⟨n,h⟩
      let a := Itinerary.run pivot m n
      undoColumnWord k (pivot k) a (Ring.inverse (a (pivot k) k)) ++ rest
    else rest

theorem undoItinerary_apply (pivot : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R)
    (n : ℕ) (x : Fin d → R) :
    (undoItinerary pivot m n).foldl (fun y op => op.apply y) (Itinerary.run pivot m n *ᵥ x) = m *ᵥ x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < d
    · rw [undoItinerary,dite_eq_left h,List.foldl_append,Itinerary.run_succ _ _ _ h,← mulVec_mulVec,
        undoColumnWord_apply,ih]
    · simpa only [undoItinerary,dite_eq_right h,Itinerary.run_succ_of_not _ _ _ h] using ih

omit [CommRing R] in
private theorem addRows_children (k : Fin d) (rows : List (Fin d)) (c : Fin d → R) :
    ((rows.flatMap (fun i => addWord k i (c i))).map RowOp.children).sum ≤ 6*rows.length := by
  induction rows with
  | nil => simp
  | cons i rows ih =>
    have bound := addWord_children k i (c i)
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.length_cons,Nat.mul_succ]
    omega

theorem undoItinerary_children (pivot : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R) (n : ℕ) :
    ((undoItinerary pivot m n).map RowOp.children).sum ≤ n*(6*(d-1)+3) := by
  induction n with
  | zero => simp [undoItinerary]
  | succ n ih =>
    rw [undoItinerary,Nat.succ_mul]
    split
    · rename_i h
      let k : Fin d := ⟨n,h⟩
      let a := Itinerary.run pivot m n
      have bound := addRows_children k ((List.finRange d).erase k)
        (fun i => a (Equiv.swap k (pivot k) i) k * Ring.inverse (a (pivot k) k))
      rw [List.length_erase_of_mem (List.mem_finRange k),List.length_finRange] at bound
      simp only [undoColumnWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,RowOp.children,Nat.add_zero]
      exact (Nat.add_le_add (Nat.add_le_add_right bound 3) ih).trans_eq (Nat.add_comm ..)
    · omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback
