module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy

/-! Read numerical cell results directly from their local scatter destination.
Borrowed output suffixes do not enter any owned cell word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {A : ℕ}

/-- Numerical contract of a local output buffer. Geometry refers to the original
ambient principal system; storage addresses refer only to local cell offsets. -/
def PackedCellOutputSpec {s : ℕ} [NeZero s] (t p u l target rhsExp L : ℕ)
    (offsets : List ℕ) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (output : List (Fin (A+4))) : Prop :=
  ∀ (n : Fin offsets.length) (I : Finset (ZMod s)) (x : ZMod s → ℝ),
    SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re) →
    (lo n).val+L ≤ s →
    (∀ k < L, Interior s t (PhaseCellBand.width p u) (lo n+(k : ZMod s)) ∧ lo n+(k : ZMod s) ∈ I) →
    (∀ k < L, cell s t (lo n+(k : ZMod s)) = cell s t (lo n)) →
    (∀ k ∈ I, cell s t k = cell s t (lo n) → ∃ i < L, lo n+(i : ZMod s) = k) →
    ∀ i : Fin L,
      |(value (executionPrecision p l target rhsExp) (decodeWord
        ((output.drop ((offsets[n.val]+i.val)*executionWidth p l target rhsExp)).take
          (executionWidth p l target rhsExp)))).re-x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target

theorem packedCellScatter_word_append (N L w : ℕ) (offsets : List ℕ)
    (E X tail : List (Fin (A+4))) (hE : E.length = N*w)
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hX : offsets.length*(L*w) ≤ X.length)
    (r i : ℕ) (hr : r < offsets.length) (hi : i < L) :
    (((scatterRows (L*w) E X (packedCellGaps L w offsets))++tail).drop
      ((offsets[r]+i)*w)).take w = (X.drop ((r*L+i)*w)).take w := by
  have hf : ScatterFits (L*w) E (packedCellGaps L w offsets) := by
    simpa [packedCellGaps] using windowGaps_fits (L*w) 0 (offsets.map (·*w)) E
      (fun _ _ => Nat.zero_le _) (packedCell_offsets_disjoint L w offsets hdis)
      (packedCell_offsets_fit N L w offsets E hE hfit)
  have hx : (packedCellGaps L w offsets).length*(L*w) ≤ X.length := by
    simpa [packedCellGaps] using hX
  have hlen := (length_scatterRows (L*w) E X (packedCellGaps L w offsets) hf hx).trans hE
  have hbound : (offsets[r]+i)*w+w ≤ N*w := by
    have hj := hfit _ (List.getElem_mem hr)
    have hh := Nat.mul_le_mul_right w (show offsets[r]+i+1 ≤ N by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  have hstart : (offsets[r]+i)*w ≤ (scatterRows (L*w) E X (packedCellGaps L w offsets)).length := by
    rw [hlen]; omega
  have hword : w ≤ ((scatterRows (L*w) E X (packedCellGaps L w offsets)).drop ((offsets[r]+i)*w)).length := by
    rw [List.length_drop,hlen]; omega
  rw [List.drop_append_of_le_length hstart,List.take_append_of_le_length hword]
  exact packedCellScatter_word N L w offsets E X hE hdis hfit hX r i hr hi

theorem packedPublishedCell_accuracy {A N L s t p u l j rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (offsets : List ℕ) (hdis : offsets.Pairwise (fun a b => a+L ≤ b))
    (hlocal : ∀ a ∈ offsets, a+L ≤ N)
    (hC : ∀ n < offsets.length, ∀ k, ‖value (executionPrecision p l j rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (n : Fin offsets.length) (I : Finset (ZMod s)) (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l j rhsExp) (C n k)).re))
    (hfit : (lo n).val + L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo n + (k : ZMod s)) ∧ lo n + (k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (lo n + (k : ZMod s)) = cell s t (lo n))
    (hmax : ∀ k ∈ I, cell s t k = cell s t (lo n) → ∃ i < L, lo n + (i : ZMod s) = k)
    (i : Fin L) (E tail output : List (Fin (A+4)))
    (hE : E.length = N*executionWidth p l j rhsExp)
    (hout : output = scatterRows (L*executionWidth p l j rhsExp) E
      (cstream A (executionWidth p l j rhsExp) (publishedWords offsets.length L
        (executedOutputWords s t p u (executionPrecision p l j rhsExp) l offsets.length L
          (executionStagePrecision p l j rhsExp) (sourceExponent l j rhsExp) lo C)))
      (packedCellGaps L (executionWidth p l j rhsExp) offsets)++tail) :
    |(value (executionPrecision p l j rhsExp) (decodeWord
      ((output.drop ((offsets[n.val]+i.val)*executionWidth p l j rhsExp)).take
        (executionWidth p l j rhsExp)))).re - x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^j := by
  let w := executionWidth p l j rhsExp
  let ys := cstream A w (publishedWords offsets.length L
    (executedOutputWords s t p u (executionPrecision p l j rhsExp) l offsets.length L
      (executionStagePrecision p l j rhsExp) (sourceExponent l j rhsExp) lo C))
  have hys : offsets.length*(L*w) ≤ ys.length := by
    simp [ys,publishedWords_length,executedOutputWords_length,Nat.mul_assoc]
  have hread := packedCellScatter_word_append N L w offsets E ys tail hE hdis hlocal hys
    n.val i.val n.isLt i.isLt
  rw [hout,hread]
  simpa only [List.append_nil] using publishedCell_accuracy hA hp hst hu hαu hθ hgap hbudget
    hL hpad lo C hC n I x hx hfit hint hcell hmax i []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
