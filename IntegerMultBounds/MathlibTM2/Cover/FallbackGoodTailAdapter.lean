module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodAdapter

/-! The reversed upper elimination factor accumulates each pivot row using only forward shears. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm M8.ReversedExchange
variable {d : ℕ} {R : Type*} [CommRing R]

def goodTailRow (k : Fin d) (c : Fin d → R) (rows : List (Fin d)) : List (RowOp d R) :=
  rows.flatMap fun i => if h : k < i then [.shear i.rev k.rev (Fin.rev_lt_rev.mpr h) (c i)] else []

theorem goodTailRow_apply (k : Fin d) (c : Fin d → R) (rows : List (Fin d)) (x : Fin d → R) (j : Fin d) :
    (goodTailRow k c rows).foldl (fun y op => op.apply y) x j =
      if j = k.rev then x j + (rows.map fun i => if k < i then c i * x i.rev else 0).sum else x j := by
  induction rows generalizing x with
  | nil => simp [goodTailRow]
  | cons i rows ih =>
    by_cases h : k < i
    · let y := Function.update x k.rev (x k.rev+c i*x i.rev)
      have terms : (rows.map fun t => if k < t then c t * y t.rev else 0) =
          rows.map fun t => if k < t then c t * x t.rev else 0 := by
        apply List.map_congr_left
        intro t _
        by_cases lt : k < t
        · simp [lt,y,Function.update_of_ne (Fin.rev_lt_rev.mpr lt).ne]
        · simp [lt]
      simp only [goodTailRow,List.flatMap_cons,dite_eq_left h,List.singleton_append,List.foldl_cons]
      change (goodTailRow k c rows).foldl _ y j = _
      rw [ih,terms]
      by_cases eq : j = k.rev <;> simp [eq,y,h,Function.update_of_ne,add_assoc]
    · simpa [goodTailRow,h] using ih x

omit [CommRing R] in
theorem goodTailRow_children (k : Fin d) (c : Fin d → R) (rows : List (Fin d)) :
    ((goodTailRow k c rows).map RowOp.children).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons i rows ih =>
    by_cases h : k < i <;> simpa [goodTailRow,h,RowOp.children] using ih

theorem goodTailRow_matrix (k : Fin d) (c : Fin d → R) (zero : ∀ i, i ≤ k → c i = 0) (x : Fin d → R) :
    (goodTailRow k c (List.finRange d)).foldl (fun y op => op.apply y) x =
      (rev d * (1+rowMat k c) * rev d).mulVec x := by
  funext j
  rw [goodTailRow_apply]
  simp only [← mulVec_mulVec,rev_mulVec,add_mulVec,one_mulVec]
  have term (i : Fin d) : (if k < i then c i*x i.rev else 0) = c i*x i.rev := by
    by_cases lt : k < i
    · simp [lt]
    · simp [lt,zero i (le_of_not_gt lt)]
  simp only [term]
  by_cases eq : j = k.rev
  · subst j
    simp [rowMat,mulVec,dotProduct,List.finRange,List.sum_ofFn,List.map_ofFn,Function.comp_def]
  · have ne : j.rev ≠ k := fun h => eq (by simpa using congrArg Fin.rev h)
    simp [eq,ne,rowMat,mulVec,dotProduct]

section
variable (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
  (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)

noncomputable def goodTailWord : (n : ℕ) → n ≤ rank → List (RowOp d R)
  | 0, _ => []
  | n+1, hn =>
    let k : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
    let stage := (stageAt G rank hr minor n (by omega)).M
    goodTailWord n (by omega) ++ goodTailRow k (elimU k stage (Ring.inverse (stage k k))) (List.finRange d)

theorem goodTailWord_apply (n : ℕ) (hn : n ≤ rank) (x : Fin d → R) :
    (goodTailWord G rank hr minor n hn).foldl (fun y op => op.apply y) x =
      (rev d * (stageAt G rank hr minor n hn).U * rev d).mulVec x := by
  induction n with
  | zero =>
    change x = (rev d * (1 : Matrix (Fin d) (Fin d) R) * rev d).mulVec x
    simp [rev_mul_rev]
  | succ n ih =>
    let k : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
    let S := stageAt G rank hr minor n (by omega)
    let c := elimU k S.M (Ring.inverse (S.M k k))
    change ((_ ++ goodTailRow k c _).foldl _ x) = (rev d * ((1+rowMat k c)*S.U) * rev d).mulVec x
    rw [List.foldl_append,ih,goodTailRow_matrix _ _ (elimU_zero k S.cleared _),mulVec_mulVec]
    simp only [Matrix.mul_assoc,rev_mul_rev_mul,c,S]

theorem goodTailWord_inverse_apply (n : ℕ) (hn : n ≤ rank) (x : Fin d → R) :
    (inverseWord (goodTailWord G rank hr minor n hn)).foldl (fun y op => op.apply y) x =
      (rev d * (stageAt G rank hr minor n hn).U' * rev d).mulVec x := by
  let S := stageAt G rank hr minor n hn
  let y := (rev d * S.U' * rev d).mulVec x
  have undo := inverseWord_apply (goodTailWord G rank hr minor n hn) y
  rw [goodTailWord_apply] at undo
  have cancel : (rev d * S.U * rev d).mulVec y = x := by
    simp only [y,mulVec_mulVec,Matrix.mul_assoc,rev_mul_rev_mul]
    rw [← Matrix.mul_assoc S.U,S.right,Matrix.one_mul,rev_mul_rev,one_mulVec]
  change (inverseWord _).foldl _ ((rev d * S.U * rev d).mulVec y) = y at undo
  rwa [cancel] at undo

theorem goodTailWord_children (n : ℕ) (hn : n ≤ rank) :
    ((goodTailWord G rank hr minor n hn).map RowOp.children).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [goodTailWord,List.sum_append,goodTailRow_children,ih]

end

end IntegerMultBounds.MathlibTM2.Cover.Fallback
