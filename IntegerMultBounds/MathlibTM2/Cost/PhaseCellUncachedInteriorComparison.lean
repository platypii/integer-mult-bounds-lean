module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloInteriorGeometryCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellWeightSetupPolynomial

/-! Compare the actual constructor's uncached interior ledger with retained
family arithmetic, charging the extra weight work explicitly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem sizedClosedBatchBound_zero_cached_le (p l L s t u target rhsExp : ℕ) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    sizedClosedBatchBound p l 0 L s t u target rhsExp ≤
      cachedClosedBatchCost p l 0 L s t u target rhsExp+
        sharedBatchWeightSetupCost P s t u q L w 0+1000*(P+N+q+l+w+1) := by
  dsimp only
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    dsimp only [executionPrecision,executionWidth]; omega
  simp only [sizedClosedBatchBound,cachedClosedBatchCost,cachedGeneratedBatchSetupCost,
    cachedBatchWeightedSetupCost,preparedBatchWeightedSetupCost,sharedBatchWeightSetupCost,
    Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  simp only [hw]
  omega

theorem haloClassSharedCost_cached_le (p l L s t u target rhsExp a b : ℕ) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    haloClassSharedCost p l L s t u target rhsExp a b ≤
      cachedHaloClassSharedCost p l L s t u target rhsExp a b+
        sharedBatchWeightSetupCost P s t u q L w 0+1000*(P+N+q+l+w+1) := by
  have h := sizedClosedBatchBound_zero_cached_le p l L s t u target rhsExp
  dsimp only at h ⊢
  dsimp only [haloClassSharedCost,cachedHaloClassSharedCost]
  omega

theorem haloInteriorCostBound_cached_le {s t : ℕ} [NeZero s]
    (p l u target rhsExp a b : ℕ) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth P q w t u
    let extra := fun L => sharedBatchWeightSetupCost P s t u q L w 0+1000*(P+N+q+l+w+1)
    haloInteriorCostBound p l s t u target rhsExp a b ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b+
        ((haloLengthCandidates s t band a b).map extra).sum+
        s*((310*P+124)*tblC V w+92*w+45)+
        (t-s+1)*(3*tblC V w+8*V+200) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let extra := fun L => sharedBatchWeightSetupCost P s t u q L w 0+1000*(P+N+q+l+w+1)
  have hclass (L : ℕ) : haloClassSharedCost p l L s t u target rhsExp a b ≤
      cachedHaloClassSharedCost p l L s t u target rhsExp a b+extra L := by
    exact (haloClassSharedCost_cached_le p l L s t u target rhsExp a b).trans_eq (Nat.add_assoc _ _ _)
  have hsum := List.sum_le_sum (l := haloLengthCandidates s t band a b) (fun L _ => hclass L)
  have hsum' : ((haloLengthCandidates s t band a b).map (fun L => haloClassSharedCost p l L s t u target rhsExp a b)).sum ≤
      ((haloLengthCandidates s t band a b).map (fun L => cachedHaloClassSharedCost p l L s t u target rhsExp a b)).sum+
        ((haloLengthCandidates s t band a b).map extra).sum :=
    hsum.trans_eq (List.sum_map_add (f := fun L => cachedHaloClassSharedCost p l L s t u target rhsExp a b) (g := extra))
  have hI : (haloInterior s t band a b).card ≤ s := by simpa using (haloInterior s t band a b).card_le_univ
  have hvol := Nat.mul_le_mul_right ((310*P+124)*tblC V w+92*w+45) hI
  dsimp only [haloInteriorCostBound,familyHaloInteriorGeometryCost,haloClassCellCost,cachedHaloClassCellCost,
    batchCoordinateCost,cachedBatchCoordinateCost,batchCellCost,cachedBatchCellCost]
  dsimp only [P,N,q,w,band,V,extra] at hsum' hvol ⊢
  nlinarith only [hsum',hvol]

end IntegerMultBounds.MathlibTM2.Cost
