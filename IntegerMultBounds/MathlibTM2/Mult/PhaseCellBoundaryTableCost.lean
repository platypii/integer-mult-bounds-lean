module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnCollectionCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryFactor

/-! A uniform construction bill for every generated Schur column and the complete factor page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def tableColumnCostBound (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let V := publicationGeometryWidth t band
  retainedIndexedColumnCost p u l s t a b target B.card s+
    columnCollectionCostBound q V s B.card band

theorem tableColumnCost_le {s : ℕ} [NeZero s] (p u l t a b target n x : ℕ)
    (hn : n < (haloBoundary s t (PhaseCellBand.width p u) a b).card) (hx : x < s) :
    tableColumnCost p u l s t a b target n x ≤ tableColumnCostBound p u l s t a b target := by
  have hcollect := retainedColumnCollectionCost_le
    (haloBoundary s t (PhaseCellBand.width p u) a b)
    (executionPrecision p l (initialSchurTarget p u target 2) 2)
    (publicationGeometryWidth t (PhaseCellBand.width p u)) (PhaseCellBand.width p u) n hn
  have hindex : retainedIndexedColumnCost p u l s t a b target n x ≤
      retainedIndexedColumnCost p u l s t a b target
        (haloBoundary s t (PhaseCellBand.width p u) a b).card s := by
    have hnV := Nat.mul_le_mul_right (12*publicationGeometryWidth t (PhaseCellBand.width p u)+11)
      (Nat.le_of_lt hn)
    dsimp only [retainedIndexedColumnCost,indexedSchurColumnCost,generatedSchurColumnCost,
      restoredOriginalColumnCost]
    omega
  dsimp only [tableColumnCost,tableColumnCostBound]
  omega

noncomputable def constructedBoundaryTableCostBound (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  prepareBoundaryPageCost s t (PhaseCellBand.width p u) a b+
    N*(tableColumnCostBound p u l s t a b target+4)+10*N+13

theorem constructedBoundaryTableCost_le (p u l s t a b target : ℕ) [NeZero s] :
    constructedBoundaryTableCost p u l s t a b target ≤
      constructedBoundaryTableCostBound p u l s t a b target := by
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  have hsum : (∑ n ∈ Finset.range B.card,
      (tableColumnCost p u l s t a b target n (bFoldAt s B n).val+1+3)) ≤
        B.card*(tableColumnCostBound p u l s t a b target+4) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range B.card, (tableColumnCostBound p u l s t a b target+4) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := tableColumnCost_le p u l t a b target n (bFoldAt s B n).val
          (Finset.mem_range.mp hn) (bFoldAt s B n).val_lt
        omega
      _ = _ := by simp
  dsimp only [constructedBoundaryTableCost,buildBoundaryTableCost,tableColumnsLoopCost,
    constructedBoundaryTableCostBound]
  dsimp only [B] at hsum
  omega

noncomputable def constructedBoundaryFactorCostBound (p u l s t a b target rhsExp : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p target rhsExp N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  constructedBoundaryTableCostBound p u l s t a b bits+
    generatedFactorPageCost q band N+boundaryFactorSetupCost p q band N+
    bandAxisPrepCost w (12*band) (factorNewtonSteps p q) N

theorem constructedBoundaryFactorCost_le (p u l s t a b target rhsExp : ℕ) [NeZero s] :
    constructedBoundaryFactorCost p u l s t a b target rhsExp ≤
      constructedBoundaryFactorCostBound p u l s t a b target rhsExp := by
  have h := constructedBoundaryTableCost_le p u l s t a b
    (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card)
  dsimp only [constructedBoundaryFactorCost,constructedBoundaryFactorPageCost,
    constructedBoundaryFactorCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
