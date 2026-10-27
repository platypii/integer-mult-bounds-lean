module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorMatrix

/-! Transfer the emitted boundary matrix's dominance and mass to its natural factor ranks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

theorem bFoldAt_sum (B : Finset (ZMod s)) (f : ZMod s → ℝ) :
    ∑ n ∈ Finset.range B.card, f (bFoldAt s B n) = ∑ j ∈ B, f j := by
  apply Finset.sum_bij (fun n _ => bFoldAt s B n)
  · intro n hn
    exact bFoldAt_mem s B n (Finset.mem_range.mp hn)
  · intro n hn m hm hnm
    have h := congrArg (bFoldPos s B) hnm
    simpa only [bFoldPos_bFoldAt s B n (Finset.mem_range.mp hn),
      bFoldPos_bFoldAt s B m (Finset.mem_range.mp hm)] using h
  · intro j hj
    exact ⟨bFoldPos s B j,Finset.mem_range.mpr (bFoldPos_lt s B j hj),bFoldAt_bFoldPos s B j hj⟩
  · intro _ _; rfl

theorem factorRankMatrix_stageInv (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (μ mass : ℝ)
    (hM : StageInv (bandBoundaryTable B W (computedBoundaryTable A q w B columns)) B μ mass) :
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card) μ mass := by
  let R := bandBoundaryTable B W (computedBoundaryTable A q w B columns)
  let M := factorRankMatrix A q w B W columns
  have hval (m n : ℕ) (hm : m < B.card) (hn : n < B.card) :
      M m n = R (bFoldAt s B m) (bFoldAt s B n) := by simp [M,R,factorRankMatrix,hm,hn]
  have hsum (m : ℕ) (hm : m < B.card) :
      ∑ n ∈ Finset.range B.card, |M m n| = ∑ j ∈ B, |R (bFoldAt s B m) j| := by
    calc
      _ = ∑ n ∈ Finset.range B.card, |R (bFoldAt s B m) (bFoldAt s B n)| := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hval m n hm (Finset.mem_range.mp hn)]
      _ = _ := bFoldAt_sum B (fun j => |R (bFoldAt s B m) j|)
  constructor
  · intro m hm
    have hm' := Finset.mem_range.mp hm
    have hi := bFoldAt_mem s B m hm'
    have hd := hM.1 (bFoldAt s B m) hi
    have he := Finset.sum_erase_add (Finset.range B.card) (fun n => |M m n|) hm
    have hf := Finset.sum_erase_add B (fun j => |R (bFoldAt s B m) j|) hi
    have hdiag := hval m m hm' hm'
    have ht := hsum m hm'
    change μ+∑ n ∈ (Finset.range B.card).erase m, |M m n| ≤ M m m
    rw [hdiag,ht] at he
    have hoff : (∑ n ∈ (Finset.range B.card).erase m, |M m n|) =
        ∑ j ∈ B.erase (bFoldAt s B m), |R (bFoldAt s B m) j| := by linarith only [he,hf]
    rw [hdiag,hoff]
    exact hd
  · intro m hm
    change ∑ n ∈ Finset.range B.card, |M m n| ≤ mass
    rw [hsum m (Finset.mem_range.mp hm)]
    exact hM.2 _ (bFoldAt_mem s B m (Finset.mem_range.mp hm))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
