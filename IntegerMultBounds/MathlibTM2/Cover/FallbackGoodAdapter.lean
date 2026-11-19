module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUndoItinerary

/-! Forward-shear schedules for the weighted head adapters of a good record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm
variable {R : Type*} [CommRing R] {d : ℕ}

/-- A good pivot clears only rows below the diagonal. Its weighted column
therefore consists entirely of forward shears, in the physical row order. -/
def goodColumnWord (k : Fin d) (c : Fin d → R) : List (RowOp d R) :=
  ((List.finRange d).filter (k < ·)).flatMap fun i => addWord k i (c i)

theorem goodColumnWord_apply (k : Fin d) (c : Fin d → R) (x : Fin d → R) (i : Fin d) :
    (goodColumnWord k c).foldl (fun y op => op.apply y) x i =
      if k < i then x i+c i*x k else x i := by
  simpa [goodColumnWord] using addRows_apply k ((List.finRange d).filter (k < ·))
    ((List.nodup_finRange d).filter _) (by simp) c x i

omit [CommRing R] in
theorem goodColumnWord_children (k : Fin d) (c : Fin d → R) :
    ((goodColumnWord k c).map RowOp.children).sum = 0 := by
  apply List.sum_eq_zero_iff.mpr
  intro n hn
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hn
  obtain ⟨i,hi,step⟩ := List.mem_flatMap.mp hop
  have lt := (List.mem_filter.mp hi).2
  simp [addWord,of_decide_eq_true lt] at step
  simp [step,RowOp.children]

/-- Each archived pivot contributes one column to the incoming head adapter,
with the original row and column weights on the shear coefficient. -/
noncomputable def goodHeadWord (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (α α' : Fin d → R) : (n : ℕ) → n ≤ rank → List (RowOp d R)
  | 0, _ => []
  | n+1, hn =>
    let k : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
    let M := (stageAt G rank hr minor n (by omega)).M
    goodHeadWord G rank hr minor α α' n (by omega) ++
      goodColumnWord k (fun i => -(α i * (M i k * Ring.inverse (M k k)) * α' k))

theorem goodHeadWord_apply (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (α α' : Fin d → R) (inv : ∀ i, α i * α' i = 1) (x : Fin d → R) (n : ℕ) (hn : n ≤ rank) :
    (goodHeadWord G rank hr minor α α' n hn).foldl (fun y op => op.apply y) x =
      (diagonal α * (stageAt G rank hr minor n hn).L' * diagonal α').mulVec x := by
  induction n with
  | zero =>
    change x = (diagonal α * 1 * diagonal α').mulVec x
    simp [diagonal_mul_diagonal,inv,diagonal_one]
  | succ n ih =>
    let k : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
    let S := stageAt G rank hr minor n (by omega)
    let c := elimL k S.M (Ring.inverse (S.M k k))
    change ((_ ++ goodColumnWord k _).foldl _ x) =
      (diagonal α * ((1-colMat k c)*S.L') * diagonal α').mulVec x
    rw [List.foldl_append,ih]
    let y := S.L'.mulVec ((diagonal α').mulVec x)
    funext i
    rw [goodColumnWord_apply]
    simp only [← mulVec_mulVec,sub_mulVec,one_mulVec,mulVec_diagonal]
    change (if k < i then α i*y i + _ * (α k*y k) else α i*y i) =
      α i*(y i-(colMat k c *ᵥ y) i)
    have entry : (colMat k c *ᵥ y) i = c i * y k := by simp [colMat,mulVec,dotProduct,ite_mul]
    rw [entry]
    split
    · rename_i lt
      have cancel : α' k * α k = 1 := (mul_comm ..).trans (inv k)
      simp only [c,elimL,ite_eq_right lt.ne']
      linear_combination -(α i * (S.M i k * Ring.inverse (S.M k k)) * y k) * cancel
    · rename_i le
      rw [show c i = 0 from elimL_zero k S.cleared _ i (le_of_not_gt le)]
      ring

theorem goodHeadWord_children (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (α α' : Fin d → R) (n : ℕ) (hn : n ≤ rank) :
    ((goodHeadWord G rank hr minor α α' n hn).map RowOp.children).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [goodHeadWord,List.sum_append,ih,goodColumnWord_children]

/-- Each stage touches at most one row per coordinate. -/
theorem goodHeadWord_length (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (α α' : Fin d → R) (n : ℕ) (hn : n ≤ rank) :
    (goodHeadWord G rank hr minor α α' n hn).length ≤ n*d := by
  have col (k : Fin d) (c : Fin d → R) : (goodColumnWord k c).length ≤ d := by
    have length (xs : List (Fin d)) (above : ∀ i ∈ xs, k < i) :
        (xs.flatMap fun i => addWord k i (c i)).length = xs.length := by
      induction xs with
      | nil => rfl
      | cons i xs ih =>
        rw [List.flatMap_cons,List.length_append,ih (fun j hj => above j (List.mem_cons_of_mem _ hj))]
        simp [addWord,above i List.mem_cons_self,Nat.add_comm]
    unfold goodColumnWord
    rw [length _ (fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2)]
    exact (List.length_filter_le ..).trans_eq (List.length_finRange (n := d))
  induction n with
  | zero => simp [goodHeadWord]
  | succ n ih =>
    simp only [goodHeadWord,List.length_append,Nat.succ_mul]
    exact Nat.add_le_add (ih _) (col ..)

def RowOp.inverse : RowOp d R → RowOp d R
  | .shear i j h c => .shear i j h (-c)
  | .swap i j => .swap i j

private theorem RowOp.inverse_apply (op : RowOp d R) (x : Fin d → R) :
    op.inverse.apply (op.apply x) = x := by
  cases op with
  | swap i j => funext k; simp [RowOp.inverse,RowOp.apply,Function.comp_def]
  | shear i j h c =>
    funext k
    by_cases eq : k = j
    · subst k; simp [RowOp.inverse,RowOp.apply,h.ne]
    · simp [RowOp.inverse,RowOp.apply,Function.update_of_ne eq]

def inverseWord (ops : List (RowOp d R)) := ops.reverse.map RowOp.inverse

theorem inverseWord_apply (ops : List (RowOp d R)) (x : Fin d → R) :
    (inverseWord ops).foldl (fun y op => op.apply y) (ops.foldl (fun y op => op.apply y) x) = x := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [inverseWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.foldl_append,
      List.foldl_cons,List.foldl_nil]
    exact (congrArg op.inverse.apply (ih (op.apply x))).trans (op.inverse_apply x)

theorem inverseWord_children (ops : List (RowOp d R)) :
    ((inverseWord ops).map RowOp.children).sum = (ops.map RowOp.children).sum := by
  have same (op : RowOp d R) : op.inverse.children = op.children := by cases op <;> rfl
  simp [inverseWord,List.map_map,Function.comp_def,same]

/-- The outgoing head adapter reads the same stages in the opposite order,
with negated shear coefficients. -/
theorem goodHeadWord_inverse_apply (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (α α' : Fin d → R) (inv : ∀ i, α i * α' i = 1) (x : Fin d → R) (n : ℕ) (hn : n ≤ rank) :
    (inverseWord (goodHeadWord G rank hr minor α α' n hn)).foldl (fun y op => op.apply y) x =
      (diagonal α * (stageAt G rank hr minor n hn).L * diagonal α').mulVec x := by
  let S := stageAt G rank hr minor n hn
  let y := (diagonal α * S.L * diagonal α').mulVec x
  have undo := inverseWord_apply (goodHeadWord G rank hr minor α α' n hn) y
  rw [goodHeadWord_apply _ _ _ _ _ _ inv] at undo
  have diag := Weighted.diagonal_inv_mul α' α (fun i => (mul_comm ..).trans (inv i))
  have cancel : (diagonal α * S.L' * diagonal α').mulVec y = x := by
    simp only [y,mulVec_mulVec]
    rw [show diagonal α * S.L' * diagonal α' * (diagonal α * S.L * diagonal α') =
      diagonal α * (S.L' * (diagonal α' * diagonal α) * S.L) * diagonal α' by simp only [Matrix.mul_assoc],
      diag,Matrix.mul_one,S.left',Matrix.mul_one,Weighted.diagonal_inv_mul α α' inv,one_mulVec]
  change (inverseWord _).foldl _ ((diagonal α * S.L' * diagonal α').mulVec y) = y at undo
  rw [cancel] at undo
  exact undo

end IntegerMultBounds.MathlibTM2.Cover.Fallback
