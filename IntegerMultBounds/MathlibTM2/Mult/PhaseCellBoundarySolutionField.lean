module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient

/-! Unfold the computed boundary list into the real ambient field required by recovery. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

noncomputable def boundarySolutionField {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (solution : List GaussianInt) (i : ZMod s) : GaussianInt :=
  if i ∈ B then realPartWord (solution.getD (bFoldPos s B i) 0) else 0

@[simp] theorem boundarySolutionField_im {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (solution : List GaussianInt) (i : ZMod s) :
    (boundarySolutionField B solution i).im = 0 := by
  by_cases hi : i ∈ B <;> simp [boundarySolutionField,hi]

theorem boundarySolutionField_off {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (solution : List GaussianInt) (i : ZMod s) (hi : i ∉ B) :
    boundarySolutionField B solution i = 0 := by simp [boundarySolutionField,hi]

theorem boundarySolutionField_fits {s : ℕ} [NeZero s] (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (hfit : ∀ z ∈ solution, Fits w z) (i : ZMod s) : Fits w (boundarySolutionField B solution i) := by
  by_cases hi : i ∈ B
  · have hpos : bFoldPos s B i < solution.length := by rw [hlen]; exact bFoldPos_lt s B i hi
    rw [boundarySolutionField,ite_eq_left hi,List.getD_eq_getElem _ _ hpos]
    exact (componentWords_fits (hfit _ (List.getElem_mem hpos))).1
  · rw [boundarySolutionField_off B solution i hi]
    constructor <;> change |(0 : ℤ)| < 2^(w-1) <;> positivity

/-- Folded output accuracy transfers to ambient boundary coordinates by real projection. -/
theorem boundarySolutionField_error {s : ℕ} [NeZero s] (q : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (x : ZMod s → ℝ) (ε : ℝ)
    (herror : ∀ i < B.card,
      ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ ε) :
    ∀ i ∈ B, |(value q (boundarySolutionField B solution i)).re - x i| ≤ ε := by
  intro i hi
  have h := herror (bFoldPos s B i) (bFoldPos_lt s B i hi)
  rw [bFoldAt_bFoldPos s B i hi] at h
  have hre := (Complex.abs_re_le_norm _).trans h
  simpa only [boundarySolutionField,ite_eq_left hi,value_realPartWord_re,
    Complex.sub_re,Complex.ofReal_re] using hre

/-- Zero extension and real projection preserve the stable magnitude for recovery. -/
theorem boundarySolutionField_magnitude {s : ℕ} [NeZero s] (q E : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt)
    (hmag : ∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^E) :
    ∀ i, ‖value q (boundarySolutionField B solution i)‖ ≤ (2 : ℝ)^E := by
  intro i
  by_cases hi : i ∈ B
  · rw [boundarySolutionField,ite_eq_left hi,value_realPartWord_norm]
    exact (Complex.abs_re_le_norm _).trans (hmag _ (bFoldPos_lt s B i hi))
  · rw [boundarySolutionField_off B solution i hi]
    have hz : value q (0 : GaussianInt) = (0 : ℂ) := by apply Complex.ext <;> simp [value]
    rw [hz,norm_zero]
    positivity


/-- Once published, the ambient stream exposes the same boundary solution to recovery. -/
theorem boundarySolutionField_published_read {s : ℕ} [NeZero s] (A q w : ℕ)
    (hA : 4 ≤ A) (hw : 0 < w) (B : Finset (ZMod s)) (solution : List GaussianInt)
    (hlen : solution.length = B.card) (hfit : ∀ z ∈ solution, Fits w z)
    (tail : List (Fin (A+4))) (i : ZMod s) :
    publishedCellRead q w (0 : ZMod s)
      (cstream A w (chirpLine s (boundarySolutionField B solution))++tail) i =
        (value q (boundarySolutionField B solution i)).re := by
  exact publishedCellRead_encodedField hA hw _ tail
    (boundarySolutionField_fits w B solution hlen hfit) i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
