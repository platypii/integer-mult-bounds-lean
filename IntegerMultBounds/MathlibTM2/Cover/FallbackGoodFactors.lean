module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossEntry

/-! Recover the triangular factors from individual archived elimination stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm
variable {d : ℕ} {R : Type*} [CommRing R]

/-- Before column k is written, all columns at or beyond k are still identity
columns. Multiplying by the next elimination factor therefore only adds its column. -/
private theorem appendPivotColumn (L : Matrix (Fin d) (Fin d) R) (k : Fin d) (c : Fin d → R)
    (untouched : ∀ i t, k ≤ t → L i t = (1 : Matrix (Fin d) (Fin d) R) i t)
    (zero : ∀ t, t ≤ k → c t = 0) : L * (1+colMat k c) = L + colMat k c := by
  rw [Matrix.mul_add,Matrix.mul_one]
  congr 1
  ext i j
  rw [mul_apply]
  have term (t : Fin d) : L i t * colMat k c t j = (1 : Matrix (Fin d) (Fin d) R) i t * colMat k c t j := by
    by_cases h : k ≤ t
    · rw [untouched i t h]
    · simp [colMat,zero t (le_of_not_ge h)]
  simp only [term,← mul_apply,Matrix.one_mul]

variable (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
  (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)

/-- Both factors use the same archive. Column j of L and row j of U are
written at stage j, and every later pivot leaves them intact. -/
theorem archivedFactors (n : ℕ) (hn : n ≤ rank) (i j : Fin d) :
    let S := stageAt G rank hr minor n hn
    let corrections := if h : j.val < n then
      let B := (stageAt G rank hr minor j.val (by omega)).M
      (elimL j B (Ring.inverse (B j j)) i, elimU j B (Ring.inverse (B j j)) i)
      else (0,0)
    S.L i j = (1 : Matrix (Fin d) (Fin d) R) i j + corrections.1 ∧
      S.U j i = (1 : Matrix (Fin d) (Fin d) R) j i + corrections.2 := by
  induction n generalizing i j with
  | zero => simp [stageAt]
  | succ n ih =>
    let k : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
    let S := stageAt G rank hr minor n (by omega)
    let v := Ring.inverse (S.M k k)
    have lower (a t : Fin d) (h : k ≤ t) : S.L a t = (1 : Matrix (Fin d) (Fin d) R) a t := by
      simpa [show ¬ t.val < n from not_lt_of_ge h] using (ih (by omega) a t).1
    have upper (a t : Fin d) (h : k ≤ t) : S.Uᵀ a t = (1 : Matrix (Fin d) (Fin d) R) a t := by
      simpa [transpose_apply,Matrix.one_apply,eq_comm,show ¬ t.val < n from not_lt_of_ge h] using (ih (by omega) a t).2
    have lc := appendPivotColumn S.L k (elimL k S.M v) lower (elimL_zero k S.cleared v)
    have uc : (1 + rowMat k (elimU k S.M v))*S.U = S.U + rowMat k (elimU k S.M v) := by
      apply Matrix.transpose_injective
      simpa only [transpose_mul,transpose_add,transpose_one,rowMat_transpose] using
        appendPivotColumn S.Uᵀ k (elimU k S.M v) upper (elimU_zero k S.cleared v)
    dsimp only
    change (S.L * (1+colMat k (elimL k S.M v))) i j = _ ∧ ((1+rowMat k (elimU k S.M v))*S.U) j i = _
    rw [lc,uc]
    by_cases eq : j = k
    · subst j
      simp [Matrix.add_apply,colMat,rowMat,lower i k le_rfl, show S.U k i = (1 : Matrix (Fin d) (Fin d) R) k i by
        simpa [Matrix.one_apply,eq_comm] using upper i k le_rfl,k,S,v]
    · have before : (j.val < n+1) = (j.val < n) := propext (by
        have ne : j.val ≠ n := fun h => eq (Fin.ext h)
        omega)
      simpa [Matrix.add_apply,colMat,rowMat,eq,before,S] using ih (by omega) i j

/-- In a mixed active/inactive block only one factor contributes. -/
theorem mixedFactorProduct (i j : Fin d) :
    let S := stageAt G rank hr minor rank le_rfl
    (rank ≤ i.val → (S.U*S.L) i j = S.L i j) ∧ (rank ≤ j.val → (S.U*S.L) i j = S.U i j) := by
  intro S
  constructor
  · intro hi
    have row (k : Fin d) : S.U i k = (1 : Matrix (Fin d) (Fin d) R) i k := by
      simpa [not_lt_of_ge hi] using (archivedFactors G rank hr minor rank le_rfl k i).2
    rw [mul_apply]
    simp only [row,← mul_apply,Matrix.one_mul]
  · intro hj
    have col (k : Fin d) : S.L k j = (1 : Matrix (Fin d) (Fin d) R) k j := by
      simpa [not_lt_of_ge hj] using (archivedFactors G rank hr minor rank le_rfl k j).1
    rw [mul_apply]
    simp only [col,← mul_apply,Matrix.mul_one]

open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear IntegerMultBounds.Swap.PivotRank in
/-- On two active coordinates the partial-permutation identity makes the
correction vanish, including at the matched pivot itself. -/
theorem activeCorrection_zero (rank : ℕ) (B : Matrix (Fin d) (Fin d) R) (i j : Fin d)
    (hi : i.rev.val < rank) (hj : j.val < rank) :
    let P : Matrix (Fin d) (Fin d) R := pivotMatrix (revPivots d rank)
    P * B * P = P → kMat P B i j = 0 := by
  intro P normalize
  have entry (a b : Fin d) : P a b = if a.val < rank ∧ b = a.rev then 1 else 0 := by
    simp only [P,pivotMatrix_apply _ ((revPivots_fst d rank).of_map _),mem_revPivots]
  have row (t : Fin d) : (P*B) i.rev t = B i t := by
    simp only [mul_apply,entry,hi,true_and,Fin.rev_rev,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have col (t : Fin d) : P t j.rev = if t = j then 1 else 0 := by
    by_cases eq : t = j
    · simp [entry,eq,hj]
    · simp [entry,eq,Ne.symm eq]
  have block := congrArg (fun X : Matrix (Fin d) (Fin d) R => X i.rev j.rev) normalize
  change (P*B*P) i.rev j.rev = P i.rev j.rev at block
  rw [mul_apply] at block
  simp only [row,col,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at block
  rw [show kMat P B i j = _ from reversedCorrection_entry rank B i j]
  simp only [hj,ite_true,true_and,sub_eq_zero]
  rw [block]
  have flip : i.rev = j ↔ i = j.rev := ⟨fun h => by simpa using congrArg Fin.rev h,fun h => by simpa using congrArg Fin.rev h⟩
  simp only [flip]

open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear in
theorem goodCross_mixed_entry (δ δ' inv : Fin d → R) (cancel : ∀ j, δ j * δ' j = 1) (i j : Fin d) :
    let S := stageAt G rank hr minor rank le_rfl
    let P : Matrix (Fin d) (Fin d) R := pivotMatrix (revPivots d rank)
    let B := rev d * S.U * rev d * rev d * (S.L * diagonal δ)
    P * B * P = P →
    (kMat P B * diagonal (fun j => inv j * δ' j)) i j =
      if j.val < rank then (if i.rev.val < rank then 0 else S.L i.rev j * inv j)
      else (if i.rev.val < rank then -(S.U i.rev j * inv j) else 0) := by
  intro S P B normalize
  by_cases hj : j.val < rank
  · by_cases hi : i.rev.val < rank
    · rw [mul_diagonal,activeCorrection_zero rank B i j hi hj normalize,zero_mul]
      simp only [hj,hi,ite_true]
    · have ne : i ≠ j.rev := fun h => hi (by simpa [h] using hj)
      rw [goodCross_entry rank S.L S.U δ δ' inv cancel]
      have prod : (S.U*S.L) i.rev j = S.L i.rev j := (mixedFactorProduct G rank hr minor i.rev j).1 (le_of_not_gt hi)
      simp only [hj,hi,ne,ite_true,ite_false,and_false,sub_zero,prod]
  · rw [goodCross_entry rank S.L S.U δ δ' inv cancel]
    have prod : (S.U*S.L) i.rev j = S.U i.rev j := (mixedFactorProduct G rank hr minor i.rev j).2 (le_of_not_gt hj)
    simp only [hj,ite_false,false_and,sub_zero,prod]

/-- In idempotent coordinates the middle matrix is an inner inverse of the pivot map. -/
private theorem pivot_normalized (X X' P Y Y' : Matrix (Fin d) (Fin d) R)
    (left : X'*X = 1) (right : Y*Y' = 1)
    (idem : (X*P*Y)*(X*P*Y) = X*P*Y) : P*(Y*X)*P = P := by
  have cancel (Z : Matrix (Fin d) (Fin d) R) : X'*(X*Z*Y)*Y' = Z := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,left,Matrix.one_mul,Matrix.mul_assoc,right,Matrix.mul_one]
  rw [show X*P*Y*(X*P*Y) = X*(P*(Y*X)*P)*Y by simp only [Matrix.mul_assoc]] at idem
  simpa only [cancel] using congrArg (fun Z => X'*Z*Y') idem

open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear in
/-- Only mixed blocks contribute: one archived off-diagonal entry, one pivot
reciprocal and the incoming inverse weight of the source coordinate. -/
theorem archivedCross_entry (idem : G*G = G)
    (A : Matrix (Fin d) (Fin rank) R) (B : Matrix (Fin rank) (Fin d) R) (factor : G = A*B)
    (inv : Fin d → R) (i j : Fin d) :
    let S := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then S.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (S.M t t) else 1
    let P : Matrix (Fin d) (Fin d) R := pivotMatrix (revPivots d rank)
    let middle := rev d * S.U * rev d * rev d * (S.L * diagonal δ)
    let K := kMat P middle * diagonal (fun t => inv t * δ' t)
    K i j = if hj : j.val < rank then
        if i.rev.val < rank then 0 else
          let N := (stageAt G rank hr minor j.val hj.le).M
          N i.rev j * Ring.inverse (N j j) * inv j
      else if hi : i.rev.val < rank then
        let N := (stageAt G rank hr minor i.rev.val hi.le).M
        Neg.neg (Ring.inverse (N i.rev i.rev) * N i.rev j * inv j)
      else 0 := by
  intro S δ δ' P middle K
  let X := S.L * diagonal δ
  let Y := rev d * S.U * rev d * rev d
  obtain ⟨_,_,undo,_,units,form⟩ := S.normalForm hr A B factor
  have diag : diagonal δ' * diagonal δ = 1 := Weighted.diagonal_inv_mul δ' δ (fun j => (mul_comm ..).trans (units j))
  have left : (diagonal δ' * S.L')*X = 1 := by
    simp only [X,Matrix.mul_assoc,← Matrix.mul_assoc S.L' S.L,S.left',Matrix.one_mul,diag]
  have right : Y*(rev d*(rev d*S.U'*rev d)) = 1 := by
    change (rev d*S.U*rev d)*rev d*(rev d*(rev d*S.U'*rev d)) = 1
    rw [Matrix.mul_assoc,rev_mul_rev_mul]
    exact undo
  have form' : X*P*Y = G := by
    change X*P*((rev d*S.U*rev d)*rev d) = G
    rw [← Matrix.mul_assoc,show X*P*(rev d*S.U*rev d) = G*rev d from form.symm,
      Matrix.mul_assoc,rev_mul_rev,Matrix.mul_one]
  have norm : P*middle*P = P := pivot_normalized X _ P Y _ left right (by rw [form',idem])
  rw [show K i j = _ from goodCross_mixed_entry G rank hr minor δ δ' inv units i j norm]
  by_cases hj : j.val < rank <;> by_cases hi : i.rev.val < rank
  · simp only [hi,hj,ite_true,dite_eq_left]
  · have ne : i.rev ≠ j := fun e => hi (e ▸ hj)
    have l := (archivedFactors G rank hr minor rank le_rfl i.rev j).1
    simp only [hj,dite_eq_left,Matrix.one_apply,ne,ite_false,zero_add,elimL] at l
    simpa only [hj,hi,ite_true,ite_false,dite_eq_left] using congrArg (· * inv j) l
  · have ne : j ≠ i.rev := fun e => hj (e ▸ hi)
    have u := (archivedFactors G rank hr minor rank le_rfl j i.rev).2
    simp only [hi,dite_eq_left,Matrix.one_apply,Ne.symm ne,ne,ite_false,zero_add,elimU] at u
    simpa only [hj,hi,ite_false,ite_true,dite_false,dite_eq_left] using congrArg (fun z => -(z*inv j)) u
  · simp only [hj,hi,ite_false,dite_false]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
