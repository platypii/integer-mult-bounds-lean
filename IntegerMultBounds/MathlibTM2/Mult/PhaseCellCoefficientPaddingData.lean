module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTilePaddingData

/-! Zero replica padding is preserved by the actual complex word encoding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

/-- Encoding padded coefficients gives exactly the padding program's symbol word. -/
theorem cstream_tilePrefixPad (A w capacity : ℕ) (xs : List GaussianInt) :
    cstream A w (tilePrefixPad capacity 0 xs) =
      tilePrefixPad (capacity*w) (pairSym A false false) (cstream A w xs) := by
  have hz : csyms A w 0 = List.replicate w (pairSym A false false) := by
    simp [csyms,coeffSyms,red]
  simp [tilePrefixPad,cstream,hz,List.flatMap_replicate,
    List.flatten_replicate_replicate,←Nat.sub_mul]

/-- The padded coefficient array contains whole zero replicas before the real
ones. Its symbol encoding is the actual prefix generated on the tape. -/
theorem coefficientPadding_view {N K L : ℕ} (A w C : ℕ)
    (f : Fin N → Fin K → Fin L → GaussianInt) (hN : N ≤ C) :
    ∃ g : Fin C → Fin K → Fin L → GaussianInt,
      replicaKeyWords g = tilePrefixPad (C*(K*L)) 0 (replicaKeyWords f) ∧
      cstream A w (replicaKeyWords g) =
        tilePrefixPad (C*(K*(L*w))) (pairSym A false false) (cstream A w (replicaKeyWords f)) ∧
      (replicaKeyWords g).drop ((C-N)*(K*L)) = replicaKeyWords f := by
  obtain ⟨g,hg⟩ := tilePrefixPad_replica_view C (0 : GaussianInt) f hN
  refine ⟨g,hg,?_,?_⟩
  · rw [hg,cstream_tilePrefixPad]
    simp only [Nat.mul_assoc]
  · rw [hg,tilePrefixPad_replica_rows]
    simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
