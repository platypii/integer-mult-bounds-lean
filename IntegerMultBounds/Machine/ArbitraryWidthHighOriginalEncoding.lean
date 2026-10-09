import IntegerMultBounds.Machine.ArbitraryWidthHighFoldSemantics
import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeJoinEncoding

/-! Exact source-tape endpoints for the arbitrary original descriptor. Folding
prefix factors changes no serialized cell, before or after the full transpose. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighOriginalEncoding
noncomputable section
open Networks
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)
open ArbitraryWidthHighFoldSemantics (foldArray)
open ArbitraryWidthHighExchangeShared (sourceWord)

/-- The high branch consumes the literal original word without a payload copy. -/
theorem source_fold {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    sourceWord (foldArray x) = sourceWord x := by
  rw [ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq,
    ArbitraryWidthHighExchangeJoinEncoding.sourceWord_eq]
  unfold RadixHighBlockJoinLoop.word
  have he : ArbitraryWidthHighExchangeJoinEncoding.encoded (foldArray x) =
      foldArray (ArbitraryWidthHighExchangeJoinEncoding.encoded x) := rfl
  rw [he,ArbitraryWidthHighFoldSemantics.foldArray_word]

/-- The returned folded transpose is exactly the original descriptor's
transpose, for every valid positive row divisor. -/
theorem source_transpose_fold {v : Descriptor} {c : ℕ}
    (hc : 0 < c) (hd : c ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) (foldArray x)) =
      sourceWord (Shared50RecursiveNodeRows.transpose hd x) := by
  rw [ArbitraryWidthHighFoldSemantics.transpose_fold hc hd,source_fold]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighOriginalEncoding
