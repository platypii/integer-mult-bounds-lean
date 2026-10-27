module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedColumnCollection

/-! Uniform bounds for gathering the clipped folded band of a computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem columnEntryStepCost_le {q V N s n x : ℕ} (hn : n ≤ N) (hx : x ≤ s) :
    columnEntryStepCost q V n x ≤ columnEntryStepCost q V N s := by
  have hnV := Nat.mul_le_mul_right (12*V+11) hn
  have hxs := Nat.mul_le_mul_right (12*(2*q+8)+9) hx
  dsimp only [columnEntryStepCost,selectedColumnEntryCost,copyResidentEntryCost]
  omega

theorem columnEntryLoopCost_le {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V start L : ℕ) (hfit : start+L ≤ B.card) :
    columnEntryLoopCost B q V start L ≤
      L*(columnEntryStepCost q V B.card s+5)+4 := by
  have hsum : (∑ i ∈ Finset.range L,
      (columnEntryStepCost q V (start+i) (bFoldAt s B (start+i)).val+3)) ≤
        L*(columnEntryStepCost q V B.card s+3) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range L, (columnEntryStepCost q V B.card s+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiL := Finset.mem_range.mp hi
        exact Nat.add_le_add_right (columnEntryStepCost_le (by omega)
          (Nat.le_of_lt (bFoldAt s B (start+i)).val_lt)) 3
      _ = _ := by simp
  dsimp only [columnEntryLoopCost]
  nlinarith only [hsum]

def columnCollectionCostBound (q V s N band : ℕ) : ℕ :=
  let W := 12*band+1
  residentBandControlsCost N band N+
    ((2*W+1)*(columnEntryStepCost q V N s+9)+2*N+8)+
    retireResidentColumnCost q s+4*N+4

theorem retainedColumnCollectionCost_le {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band n : ℕ) (hn : n < B.card) :
    retainedColumnCollectionCost B q V band n ≤
      columnCollectionCostBound q V s B.card band := by
  let W := 12*band+1
  let start := n-W
  let L := min B.card (n+W+1)-start
  have hstart : start ≤ B.card := by dsimp [start]; omega
  have hfit : start+L ≤ B.card := by dsimp [start,L]; omega
  have hlen : L ≤ 2*W+1 := by dsimp [L,start]; omega
  have hloop := columnEntryLoopCost_le B q V start L hfit
  have hmul := Nat.mul_le_mul_right (columnEntryStepCost q V B.card s+9) hlen
  have hcontrols : residentBandControlsCost n band B.card ≤
      residentBandControlsCost B.card band B.card := by
    dsimp only [residentBandControlsCost,clippedBandControlsCost,bandIntervalEndpointsCost,clipUnaryCost]
    simp only [List.sum_cons,List.sum_nil]
    omega
  dsimp only [retainedColumnCollectionCost,collectRetireColumnCost,preparedBandCollectionCost,
    collectColumnEntriesCost,columnCollectionCostBound]
  change 4*n+4+(residentBandControlsCost n band B.card+
    (columnEntryLoopCost B q V start L+(2*(L+start)+2+(2*L+2)))+
      retireResidentColumnCost q s) ≤ _
  dsimp only [W] at hmul
  nlinarith only [hloop,hmul,hcontrols,hstart,hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
