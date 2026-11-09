module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWordStock
import Mathlib.Tactic.GCongr

/-! Uniform lookup reserves scale with packed table volume, not repeated lookup time. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

@[irreducible] def factorWordUniformWorkspace (q maxColumn maxRow W N : ℕ) : ℕ :=
  2*(100*(maxColumn+maxRow+W+N+1))+
    ((N*(2*W+1)+1000*(maxColumn+maxRow+W+N+1)+
      8*copyPackedWordCost q (N*(2*W+1)+N)+8*feedFactorWordCost q)+8*factorZeroEntryCost q)

theorem factorWordWorkspace_le_uniform (q n m maxColumn maxRow W N : ℕ)
    (hn : n ≤ maxColumn) (hm : m ≤ maxRow) :
    factorWordWorkspace q n m W N ≤ factorWordUniformWorkspace q maxColumn maxRow W N := by
  have hc : factorChoiceCost n m W N ≤ 100*(maxColumn+maxRow+W+N+1) := by
    simp only [factorChoiceCost,unaryIfLeSumCost,unaryIfLtCost]
    omega
  have hcount := (packedBandWordCount_le N W (N-(n+1)) (n+1)).trans
    (Nat.mul_le_mul_right (2*W+1) (Nat.sub_le N (n+1)))
  have hoff : packedEntryOffset N W n m ≤ N*(2*W+1)+N := by
    unfold packedEntryOffset
    omega
  have ha : generatePackedAddressWorkspace n m W N ≤ N*(2*W+1)+1000*(maxColumn+maxRow+W+N+1) := by
    apply (generatePackedAddressWorkspace_le n m W N).trans
    gcongr
  have hcopy : copyPackedWordCost q (packedEntryOffset N W n m) ≤
      copyPackedWordCost q (N*(2*W+1)+N) := by
    unfold copyPackedWordCost
    gcongr
  unfold factorWordWorkspace factorEntryWorkspace rankedBoundaryEntryWorkspace factorWordUniformWorkspace
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
