module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryScatterData

/-! The inverse-folded boundary solution is published and read over the packed
halo interval, retaining ambient indices and arbitrary borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix

noncomputable def boundaryFoldedRead {A s : ℕ} [NeZero s] (q w : ℕ)
    (B : Finset (ZMod s)) (raw : List (Fin (A+4))) (i : ZMod s) : ℂ :=
  value q (decodeWord ((raw.drop (bFoldPos s B i*w)).take w))

theorem boundaryFoldedRead_eq {A s : ℕ} [NeZero s] (hA : 4 ≤ A) (q w : ℕ) (hw : 0 < w)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hfits : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4))) (i : ZMod s) (hi : i ∈ B) :
    boundaryFoldedRead q w B (cstream A w solution++tail) i =
      value q (solution.getD (bFoldPos s B i) 0) := by
  have hpos : bFoldPos s B i < solution.length := by rw [hlen]; exact bFoldPos_lt s B i hi
  rw [boundaryFoldedRead,cstream_word w solution tail _ hpos,
    decodeWord_of_fits hA hw _ (hfits _ (List.getElem_mem hpos)),List.getD_eq_getElem _ _ hpos]

theorem boundaryFoldedRead_error {A s : ℕ} [NeZero s] (hA : 4 ≤ A) (q w : ℕ) (hw : 0 < w)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hfits : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4)))
    (x : ZMod s → ℝ) (ε : ℝ)
    (herror : ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ ε) :
    PhaseCellInterface.ErrorOn B (fun i => (boundaryFoldedRead q w B (cstream A w solution++tail) i).re) x ε := by
  intro i hi
  have hh := herror (bFoldPos s B i) (bFoldPos_lt s B i hi)
  rw [bFoldAt_bFoldPos s B i hi] at hh
  dsimp only
  rw [boundaryFoldedRead_eq hA q w hw B solution hlen hfits tail i hi]
  simpa only [Complex.sub_re,Complex.ofReal_re,Real.norm_eq_abs] using (Complex.abs_re_le_norm _).trans hh

theorem packedBoundary_scatter_solution {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (A a L w : ℕ) (hfit : a+L ≤ s)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card) :
    scatterRows w (cstream A w (List.replicate L 0))
      (cstream A w ((unfoldList solution).map realPartWord)) (packedBoundaryGaps B a w) =
      cstream A w (packedInterval a L (boundarySolutionField B solution)) := by
  rw [boundary_unfold_field B solution hlen]
  exact packedBoundary_scatter_cstream B A a L w hfit hB _
    (boundarySolutionField_off B solution)

theorem boundarySolutionField_packed_read {A s : ℕ} [NeZero s]
    (hA : 4 ≤ A) (q w a L : ℕ) (hw : 0 < w) (hfit : a+L ≤ s)
    (B : Finset (ZMod s)) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hfits : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4))) (i : ZMod s) (hi : i ∈ B) :
    packedIntervalRead q w a (cstream A w (packedInterval a L (boundarySolutionField B solution))++tail) i =
      value q (boundarySolutionField B solution i) := by
  rw [packedIntervalRead_eq q w a L _ tail [] hfit i (hB i hi).1 (hB i hi).2]
  exact pairedCellRead_encodedField hA hw _ [] i (boundarySolutionField_fits w B solution hlen hfits i)

theorem boundarySolutionField_packed_error {A s : ℕ} [NeZero s]
    (hA : 4 ≤ A) (q w a L : ℕ) (hw : 0 < w) (hfit : a+L ≤ s)
    (B : Finset (ZMod s)) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hfits : ∀ z ∈ solution, Fits w z) (tail : List (Fin (A+4)))
    (x : ZMod s → ℝ) (ε : ℝ)
    (herror : ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ ε) :
    PhaseCellInterface.ErrorOn B (fun i =>
      (packedIntervalRead q w a (cstream A w (packedInterval a L (boundarySolutionField B solution))++tail) i).re) x ε := by
  intro i hi
  dsimp only
  rw [boundarySolutionField_packed_read hA q w a L hw hfit B hB solution hlen hfits tail i hi]
  simpa only [Real.norm_eq_abs] using boundarySolutionField_error q B solution x ε herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
