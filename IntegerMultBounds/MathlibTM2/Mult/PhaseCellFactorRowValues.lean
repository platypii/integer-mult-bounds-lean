module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWord
public import IntegerMultBounds.NLogN.SchurWindow

/-! Fixed row words represent the factorizer's zero-extended boundary matrix on its exact grid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

noncomputable def factorRankMatrix (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) : Matrix ℕ ℕ ℝ :=
  fun m n => if m < B.card ∧ n < B.card then
    bandBoundaryTable B W (computedBoundaryTable A q w B columns) (bFoldAt s B m) (bFoldAt s B n) else 0

noncomputable def factorRowValues (B : Finset (ZMod s)) (W start m : ℕ)
    (columns : List (ZMod s → GaussianInt)) : List GaussianInt :=
  (List.range' start (2*W+1)).map (fun n => factorRankWord B W columns n m)

@[simp] theorem factorRowValues_length (B : Finset (ZMod s)) (W start m : ℕ)
    (columns : List (ZMod s → GaussianInt)) : (factorRowValues B W start m columns).length = 2*W+1 := by
  simp [factorRowValues]

theorem factorRankWord_value (A q w : ℕ) (B : Finset (ZMod s)) (W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    (value q (factorRankWord B W columns n m)).re = factorRankMatrix A q w B W columns m n := by
  by_cases hv : FactorRankValid B.card W n m
  · obtain ⟨hnN,hmN,hnm,hmn⟩ := hv
    have hv : FactorRankValid B.card W n m := ⟨hnN,hmN,hnm,hmn⟩
    have hn' : n < columns.length := by omega
    have hp := bFoldPos_bFoldAt s B n hnN
    have hi : bFoldPos s B (bFoldAt s B n) < columns.length := by rw [hp]; exact hn'
    have hrel : FoldBRel s B W (bFoldAt s B m) (bFoldAt s B n) := by
      simpa only [FoldBRel,bFoldPos_bFoldAt s B m hmN,hp] using And.intro hmn hnm
    rw [factorRankWord,if_pos hv,List.getD_eq_getElem _ _ hn']
    simp only [factorRankMatrix,hmN,hnN,true_and,ite_true,bandBoundaryTable,hrel,computedBoundaryTable,dif_pos hi]
    rw [getElem_congr rfl hp]
    rw [columnWordRead,decodeWord_of_fits hA hw _ ((hformat columns[n] (List.getElem_mem hn')).2 _)]
  · rw [factorRankWord,if_neg hv]
    by_cases hinside : m < B.card ∧ n < B.card
    · have hrel : ¬FoldBRel s B W (bFoldAt s B m) (bFoldAt s B n) := by
        intro hrel
        have hh : m ≤ n+W ∧ n ≤ m+W := by
          simpa only [FoldBRel,bFoldPos_bFoldAt s B m hinside.1,bFoldPos_bFoldAt s B n hinside.2] using hrel
        exact hv ⟨hinside.2,hinside.1,hh.2,hh.1⟩
      simp [factorRankMatrix,hinside,bandBoundaryTable,hrel,value]
    · simp [factorRankMatrix,hinside,value]

theorem factorRowValues_grid (A q w : ℕ) (B : Finset (ZMod s)) (W start m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    (factorRowValues B W start m columns).map (fun z => (value q z).re) =
      winRow W (factorRankMatrix A q w B W columns) start m := by
  simp only [factorRowValues,List.map_map,winRow]
  apply List.map_congr_left
  intro n _
  exact factorRankWord_value A q w B W n m columns hlen hformat hA hw

theorem factorRowValues_format (B : Finset (ZMod s)) (W w start m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) :
    ∀ z ∈ factorRowValues B W start m columns, z.im = 0 ∧ Fits w z := by
  intro z hz
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hz
  exact factorRankWord_format B W w n m columns hlen hformat

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
