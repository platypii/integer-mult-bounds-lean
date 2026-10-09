import IntegerMultBounds.Machine.CompactComplexRootPieceVisits

/-! Prefix identities for the physical outer root-digit loop. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPiecePrefixes
open CompactComplexRecursiveGeometry CompactComplexRootPieceVisits

def count (ds : List ℕ) := (expandDigits 0 ds).length

theorem preceding_append (pre : List ℕ) (digit : ℕ) :
    preceding (pre++[digit])=preceding pre+digit*arity^pre.length := by
  simp [preceding,expand_append,expandDigits,List.sum_replicate]

theorem count_append (pre : List ℕ) (digit : ℕ) : count (pre++[digit])=count pre+digit := by
  simp [count,expand_append,expandDigits]

theorem left_step (ds : List ℕ) (k : ℕ) (hk : k<ds.length) :
    preceding (ds.take (k+1))=preceding (ds.take k)+ds[k]*arity^k := by
  rw [List.take_succ_eq_append_getElem hk,preceding_append,List.length_take,Nat.min_eq_left (by omega)]

theorem count_step (ds : List ℕ) (k : ℕ) (hk : k<ds.length) :
    count (ds.take (k+1))=count (ds.take k)+ds[k] := by
  rw [List.take_succ_eq_append_getElem hk,count_append]

end IntegerMultBounds.Machine.CompactComplexRootPiecePrefixes
