module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedIndexedColumn

/-! Separate the actual interior solve and two uncached coupling passes from
ordinary Schur-column headers, indexing, projection and owned-line retirement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN

theorem retainedIndexedColumnCost_controls_le (p u l s t a b target n x : ℕ) :
    let band := PhaseCellBand.width p u
    let stage := initialSchurTarget p u target 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    let V := publicationGeometryWidth t band
    let H := 2^15*p+q+s+t+u+band+a+b+n+x+1
    retainedIndexedColumnCost p u l s t a b target n x ≤
      solveHaloInteriorCost p l s t u stage 2 a b+
        borrowedCouplingPassCost true (2^15*p) q w s t u band a b+
        borrowedCouplingPassCost false (2^15*p) q w s t u band a b+
        1000000*H*(V+w+1) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let stage := initialSchurTarget p u target 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  let V := publicationGeometryWidth t band
  let H := 2^15*p+q+s+t+u+band+a+b+n+x+1
  let R := V+w+1
  have hH : 1 ≤ H := by dsimp only [H]; omega
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hs : s ≤ H := by dsimp only [H]; omega
  have hn : n ≤ H := by dsimp only [H]; omega
  have hw : w ≤ R := by dsimp only [R]; omega
  have hV : V ≤ R := by dsimp only [R]; omega
  have hsw := Nat.mul_le_mul hs hw
  have hnV := Nat.mul_le_mul hn hV
  have hHp := Nat.le_mul_of_pos_right H hR
  have hRp := Nat.le_mul_of_pos_left R hH
  have hqw : 2*q+8 = w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  dsimp only [retainedIndexedColumnCost,indexedSchurColumnCost,generatedSchurColumnCost,
    restoredOriginalColumnCost,generatedOriginalColumnCost,originalColumnInputsCost,
    releaseColumnSourcesCost,releasedSchurResidualCost,realInteriorResidualCost,
    restoredInteriorResidualCost,initializedInteriorResidualCost,initializeInteriorOutputCost,
    interiorResidualCost,interiorForCouplingCost,feedCouplingPassCost,realResidualProjectionCost,
    retireInitialInteriorCost,releaseSchurColumnInputCost,installCouplingHeadersCost,releaseCouplingHeadersCost]
  dsimp only [band,stage,q,w,V,H,R] at hsw hnV hHp hRp hqw ⊢
  simp only [hqw]
  nlinarith only [hsw,hnV,hHp,hRp]

end IntegerMultBounds.MathlibTM2.Cost
