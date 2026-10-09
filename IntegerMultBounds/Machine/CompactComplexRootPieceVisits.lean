import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry

/-! The runtime digit-clock boundaries are exactly the canonical root Visits.
Each digit produces that many consecutive equal-width pieces; the next digit
increments the exponent and grows width by the actual fixed arity. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceVisits
noncomputable section
open CompactComplexRecursiveGeometry

theorem expand_append (start : ℕ) (pre post : List ℕ) :
    expandDigits start (pre++post)=expandDigits start pre++expandDigits (start+pre.length) post := by
  induction pre generalizing start with
  | nil => simp [expandDigits]
  | cons digit pre ih =>
    simp only [List.cons_append,expandDigits,ih,List.length_cons,List.append_assoc]
    simp only [Nat.add_comm,Nat.add_left_comm]

def preceding (pre : List ℕ) := ((expandDigits 0 pre).map (fun k => arity^k)).sum

theorem generated_visit (active : ℕ) (pre post : List ℕ) (digit j : ℕ)
    (hd : Nat.digits arity active=pre++digit::post) (hj : j<digit) :
    Visit active (preceding pre+j*arity^pre.length) pre.length := by
  have he : exponents active=expandDigits 0 pre++
      (List.replicate digit pre.length++expandDigits (pre.length+1) post) := by
    simp only [exponents,hd,expand_append,zero_add,expandDigits]
  let offset := (expandDigits 0 pre).length
  have hi : offset+j<(exponents active).length := by
    rw [he]
    simp only [List.length_append,List.length_replicate]
    dsimp [offset]
    omega
  let idx : Fin (exponents active).length := ⟨offset+j,hi⟩
  have hk : pieceExponent active idx=pre.length := by
    unfold pieceExponent
    simp only [idx]
    simp only [he]
    rw [List.getElem_append_right (by dsimp [offset]; omega)]
    simp only [show offset+j-(expandDigits 0 pre).length=j by dsimp [offset]; omega]
    rw [List.getElem_append_left (by simpa using hj),List.getElem_replicate]
  have hl : pieceLeft active idx=preceding pre+j*arity^pre.length := by
    unfold pieceLeft widths
    simp only [idx]
    rw [he,List.map_append,List.map_append,List.map_replicate]
    rw [List.take_append]
    have hs : (List.map (fun k => arity^k) (expandDigits 0 pre)).length=offset := by simp [offset]
    rw [hs]
    rw [List.take_of_length_le (by omega)]
    simp only [Nat.add_sub_cancel_left,List.sum_append]
    rw [List.take_append_of_le_length (by simp; omega),List.take_replicate,Nat.min_eq_left (by omega),List.sum_replicate]
    rfl
  have hv := Visit.root idx
  rw [hk,hl] at hv
  exact hv

end
end IntegerMultBounds.Machine.CompactComplexRootPieceVisits
