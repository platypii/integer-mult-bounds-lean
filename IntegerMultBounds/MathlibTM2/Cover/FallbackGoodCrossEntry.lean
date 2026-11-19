module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCross

/-! Entrywise correction for a reversed rank prefix, after cancellation of the pivot weights. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear (pivotMatrix)
open IntegerMultBounds.Swap.PivotRank (pivotMatrix_apply)
variable {d : ℕ} {R : Type*} [CommRing R]

theorem reversedCorrection_entry (rank : ℕ) (B : Matrix (Fin d) (Fin d) R) (i j : Fin d) :
    kMat (pivotMatrix (revPivots d rank)) B i j =
      (if j.val < rank then B i j else if i.rev.val < rank then -B i j else 0) -
        (if j.val < rank ∧ i = j.rev then 1 else 0) := by
  let ps := revPivots d rank
  have row : j ∈ ps.map Prod.fst ↔ j.val < rank := by simp [ps,revPivots,List.map_map,Function.comp_def]
  have col : i ∈ ps.map Prod.snd ↔ i.rev.val < rank := by
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,mem,rfl⟩ := List.mem_map.mp h
      obtain ⟨lt,rfl⟩ := (mem_revPivots ..).mp mem
      simpa using lt
    · intro lt
      exact List.mem_map.mpr ⟨(i.rev,i),(mem_revPivots ..).mpr ⟨lt,by simp⟩,rfl⟩
  change kMat (pivotMatrix ps) B i j = _
  simp only [kMat,pivot_mul_transpose ps (revPivots_fst ..) (revPivots_snd ..),
    transpose_mul_pivot ps (revPivots_fst ..) (revPivots_snd ..),indicator,Matrix.sub_apply,Matrix.add_apply,
    mul_diagonal,diagonal_mul,transpose_apply,pivotMatrix_apply ps ((revPivots_fst ..).of_map _),
    row,col,ps,mem_revPivots]
  by_cases a : j.val < rank <;> simp [a]
  split <;> simp_all

theorem goodCross_entry (rank : ℕ) (L U : Matrix (Fin d) (Fin d) R)
    (δ δ' inv : Fin d → R) (cancel : ∀ j, δ j * δ' j = 1) (i j : Fin d) :
    let B := rev d * U * rev d * rev d * (L * diagonal δ)
    let K := kMat (pivotMatrix (revPivots d rank)) B * diagonal (fun j => inv j * δ' j)
    K i j = (if j.val < rank then (U*L) i.rev j * inv j
             else if i.rev.val < rank then -((U*L) i.rev j * inv j) else 0) -
            (if j.val < rank ∧ i = j.rev then inv j * δ' j else 0) := by
  intro B K
  have entry : B i j = (U*L) i.rev j * δ j := by
    have eq : B = rev d * ((U*L) * diagonal δ) := by simp only [B,Matrix.mul_assoc,rev_mul_rev_mul]
    rw [eq,rev_mul_apply,mul_diagonal]
  dsimp only [K]
  rw [mul_diagonal,reversedCorrection_entry,entry,sub_mul]
  have scale : (U*L) i.rev j * δ j * (inv j * δ' j) = (U*L) i.rev j * inv j := by
    calc
      _ = ((U*L) i.rev j * inv j) * (δ j * δ' j) := by ring
      _ = _ := by rw [cancel,mul_one]
  simp only [ite_mul,one_mul,zero_mul,neg_mul,scale]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
