module

public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! The clipped folded-band schedule stores at most two half widths plus the diagonal. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellMatrix

def foldedBandIndices (rowCount W n : ℕ) : List ℕ :=
  List.range' (n-W) (min rowCount (n+W+1)-(n-W))

@[simp] theorem foldedBandIndices_length (rowCount W n : ℕ) :
    (foldedBandIndices rowCount W n).length = min rowCount (n+W+1)-(n-W) := by
  simp [foldedBandIndices]

theorem foldedBandIndices_length_le (rowCount W n : ℕ) :
    (foldedBandIndices rowCount W n).length ≤ 2*W+1 := by
  rw [foldedBandIndices_length]
  omega

theorem mem_foldedBandIndices {rowCount W n k : ℕ} (hn : n < rowCount) :
    k ∈ foldedBandIndices rowCount W n ↔ k < rowCount ∧ k ≤ n+W ∧ n ≤ k+W := by
  simp only [foldedBandIndices,List.mem_range']
  have hmin : n-W ≤ min rowCount (n+W+1) := by omega
  simp only [one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨hk,hkn,hnk⟩
    refine ⟨k-(n-W),?_,?_⟩ <;> omega

noncomputable def foldedBandRows {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W n : ℕ) : List (ZMod s) :=
  (foldedBandIndices B.card W n).map (bFoldAt s B)

theorem foldedBandRows_length_le {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W n : ℕ) :
    (foldedBandRows B W n).length ≤ 2*W+1 := by
  simpa [foldedBandRows] using foldedBandIndices_length_le B.card W n

theorem mem_foldedBandRows {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W n : ℕ)
    (hn : n < B.card) (i : ZMod s) :
    i ∈ foldedBandRows B W n ↔ i ∈ B ∧ FoldBRel s B W i (bFoldAt s B n) := by
  constructor
  · intro hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    obtain ⟨hk,hkn,hnk⟩ := (mem_foldedBandIndices hn).mp hk
    refine ⟨bFoldAt_mem s B k hk,?_⟩
    simpa only [FoldBRel,bFoldPos_bFoldAt s B k hk,bFoldPos_bFoldAt s B n hn] using And.intro hkn hnk
  · rintro ⟨hi,hrel⟩
    apply List.mem_map.mpr
    refine ⟨bFoldPos s B i,?_,bFoldAt_bFoldPos s B i hi⟩
    apply (mem_foldedBandIndices hn).mpr
    refine ⟨bFoldPos_lt s B i hi,?_⟩
    simpa only [FoldBRel,bFoldPos_bFoldAt s B n hn] using hrel


/-- Size of the packed computed entries selected for one folded band column. -/
theorem foldedBandColumn_storage {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W n A w : ℕ)
    (C : ZMod s → GaussianInt) :
    (IntegerMultBounds.MathlibTM2.Fast.cstream A w
      ((foldedBandRows B W n).map C)).length ≤ (2*W+1)*w := by
  simpa using Nat.mul_le_mul_right w (foldedBandRows_length_le B W n)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
