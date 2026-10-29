module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublishedAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellRows

/-! Transport the executed local buffer's accuracy to its ambient integer field.
Local addresses and ambient matrix coordinates remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement

theorem packedCellField_word {A s origin N L w : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw : 1 ≤ w) (D : ZMod s → GaussianInt) (hD : ∀ k, Fits w (D k))
    (offsets : List ℕ) (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (n : Fin offsets.length) (i : Fin L) :
    decodeWord (((cstream A w (packedInterval origin N D)++tail).drop
      ((offsets[n.val]+i.val)*w)).take w) = D (packedCellOrigin origin offsets n+(i.val : ZMod s)) := by
  have hn := hfit _ (List.getElem_mem n.isLt)
  have hj : offsets[n.val]+i.val < N := by omega
  rw [cstream_word w _ tail _ (by rw [packedInterval_length D hhalo]; exact hj),
    packedInterval_get D hhalo hj,decodeWord_of_fits hA hw _ (hD _)]
  congr 1
  simp [packedCellOrigin,List.getElem?_eq_getElem n.isLt,Nat.cast_add,add_assoc]

theorem packedCellOutputSpec_field_at {A s t p u l target rhsExp origin N L : ℕ} [NeZero s]
    (hA : 4 ≤ A) (D : ZMod s → GaussianInt)
    (hD : ∀ k, Fits (executionWidth p l target rhsExp) (D k))
    (offsets : List ℕ) (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (C : ℕ → ZMod s → GaussianInt) (output tail : List (Fin (A+4)))
    (hout : output = cstream A (executionWidth p l target rhsExp) (packedInterval origin N D)++tail)
    (haccuracy : PackedCellOutputSpec t p u l target rhsExp L offsets
      (packedCellOrigin (s := s) origin offsets) C output)
    (n : Fin offsets.length) (I : Finset (ZMod s)) (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (hcellfit : (packedCellOrigin (s := s) origin offsets n).val+L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u)
      (packedCellOrigin origin offsets n+(k : ZMod s)) ∧ packedCellOrigin origin offsets n+(k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (packedCellOrigin origin offsets n+(k : ZMod s)) =
      cell s t (packedCellOrigin origin offsets n))
    (hmax : ∀ k ∈ I, cell s t k = cell s t (packedCellOrigin origin offsets n) →
      ∃ i < L, packedCellOrigin origin offsets n+(i : ZMod s) = k) (i : Fin L) :
    |(value (executionPrecision p l target rhsExp)
      (D (packedCellOrigin origin offsets n+(i.val : ZMod s)))).re-
      x (packedCellOrigin origin offsets n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target := by
  have hh := haccuracy n I x hx hcellfit hint hcell hmax i
  rw [hout,packedCellField_word hA (by dsimp [executionWidth]; omega) D hD offsets hhalo hfit tail n i] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
