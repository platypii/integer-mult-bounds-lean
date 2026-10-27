module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTableValues

/-! The physical word address of a selected folded-band entry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix

variable {s : ℕ} [NeZero s]

def packedEntryOffset (rowCount W n m : ℕ) : ℕ :=
  packedBandWordCount rowCount W (rowCount-(n+1)) (n+1)+(min rowCount (n+W+1)-1-m)

theorem bandColumnValues_entry (B : Finset (ZMod s)) (W n m : ℕ)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n) (C : ZMod s → GaussianInt) :
    ∃ hk : min B.card (n+W+1)-1-m < (bandColumnValues B W n C).length,
      (bandColumnValues B W n C)[min B.card (n+W+1)-1-m] = C (bFoldAt s B m) := by
  obtain ⟨hmN,hmn,hnm⟩ := (mem_foldedBandIndices hn).mp hm
  have hstart : n-W ≤ min B.card (n+W+1) := by omega
  have hk : min B.card (n+W+1)-1-m < (bandColumnValues B W n C).length := by
    simp only [bandColumnValues,foldedBandRows,foldedBandIndices,List.length_map,List.length_reverse,List.length_range']
    omega
  refine ⟨hk,?_⟩
  simp only [bandColumnValues,foldedBandRows,foldedBandIndices,List.map_reverse,List.getElem_map,
    List.getElem_reverse,List.length_map,List.length_reverse,List.length_range',List.getElem_range']
  congr 2
  omega

theorem packedEntryOffset_entry (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card) (n m : ℕ)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n) :
    ∃ hk : packedEntryOffset B.card W n m < (bandTableValues B W columns 0).length,
      (bandTableValues B W columns 0)[packedEntryOffset B.card W n m] = columns[n] (bFoldAt s B m) := by
  have hn' : n < columns.length := by omega
  obtain ⟨hk,hentry⟩ := bandColumnValues_entry B W n m hn hm columns[n]
  have hsplit := bandTableValues_column B W columns n hn'
  have hoffset : packedEntryOffset B.card W n m =
      (bandTableValues B W (columns.drop (n+1)) (n+1)).length+(min B.card (n+W+1)-1-m) := by
    rw [bandTableValues_length,List.length_drop,hlen]
    rfl
  have hbound : packedEntryOffset B.card W n m < (bandTableValues B W columns 0).length := by
    rw [hsplit,List.length_append,List.length_append]
    rw [hoffset]
    omega
  refine ⟨hbound,?_⟩
  simp only [hsplit,hoffset,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact (List.getElem_append_left hk).trans hentry

theorem packedEntryOffset_lt (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card) (n m : ℕ)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n) :
    packedEntryOffset B.card W n m < B.card*(2*W+1) := by
  obtain ⟨hk,_⟩ := packedEntryOffset_entry B W columns hlen n m hn hm
  exact hk.trans_le (by simpa [hlen] using bandTableValues_length_le B W columns 0)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
