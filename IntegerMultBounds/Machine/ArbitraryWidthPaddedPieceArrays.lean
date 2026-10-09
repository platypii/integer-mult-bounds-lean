import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeShared
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Literal binary words at the row-padding/piece-dispatcher boundary. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceArrays
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding
open RowPaddingConstructedAlphabet (mapArray mapTape)
open ArbitraryWidthHighExchangeShared (sourceWord)

def word {n : ℕ} (x : Fin n → ZMod 2) : ℤ → Fin (prime+4) :=
  putWord (fun _ => blank) 0 (List.ofFn (fun z => SparseRoleCircuit.encode (x z)))

theorem map_encode {n : ℕ} (x : Fin n → ZMod 2) :
    mapArray (a := prime) (fun z => SparseRoleCircuit.encode (x z)) =
      fun z => SparseRoleCircuit.encode (x z) := by
  exact RowPaddingConstructedAlphabet.map_bits (fun z => decide (x z = 1))

theorem word_source {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    word x = sourceWord x := by
  change _ = FlatRepeatedControlNormalize.encoded
    (putWord (fun _ => blank) 0 (List.ofFn (Shared50RecursiveNodeSemantics.encoded x)))
  have he : FlatRepeatedControlNormalize.encoded
      (putWord (fun _ => blank) 0 (List.ofFn (Shared50RecursiveNodeSemantics.encoded x))) =
      mapTape (a := prime)
        (putWord (fun _ => blank) 0 (List.ofFn (Shared50RecursiveNodeSemantics.encoded x))) := by rfl
  rw [he,RowPaddingConstructedAlphabet.map_array_word]
  change _ = putWord (fun _ => blank) 0 (List.ofFn
    (mapArray (a := prime) (fun z => SparseRoleCircuit.encode (x z))))
  rw [map_encode]
  rfl

theorem word_rowView {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) :
    word (rowView x) = word x := by
  unfold word
  congr 1
  exact (List.ofFn_congr (volume_rows v) (fun z => SparseRoleCircuit.encode (x z))).symm

theorem encode_pad {P R R' L : ℕ} (x : Fin (P*R*L) → ZMod 2) :
    pad R' (bitSymbol false) (fun z => SparseRoleCircuit.encode (a := prime) (x z)) =
      fun z => SparseRoleCircuit.encode (pad R' 0 x z) := by
  funext z
  unfold pad
  dsimp only
  split_ifs
  · rfl
  · simp [SparseRoleCircuit.encode]

theorem encode_crop {P R R' L : ℕ} (hR : R ≤ R') (x : Fin (P*R'*L) → ZMod 2) :
    crop hR (fun z => SparseRoleCircuit.encode (a := prime) (x z)) =
      fun z => SparseRoleCircuit.encode (crop hR x z) := rfl

theorem erased_word {n : ℕ} (x : Fin n → ZMod 2) :
    RowPaddingConstructedAlphabet.erased (word x) 0 n = fun _ => blank := by
  have h := RowPaddingConstructedAlphabet.erased_array_word (a := prime)
    (fun _ => blank) 0 (fun z => SparseRoleCircuit.encode (a := 0) (x z)) (fun _ _ _ => rfl)
  rw [map_encode] at h
  exact h

end
end IntegerMultBounds.Machine.ArbitraryWidthPaddedPieceArrays
