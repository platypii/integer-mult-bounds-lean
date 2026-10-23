module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandValue
public import IntegerMultBounds.MathlibTM2.Mult.ChirpWindows
public import IntegerMultBounds.MathlibTM2.Mult.ChirpRing

/-! # Integer operands for the shared chirp convolution

Weights are arbitrary integer numerators here. Thus the representation theorem applies
both to generated tables and to the actual pointwise stream multiplication result.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- Forward weighted window, before reversing its coefficient order. -/
def chirpWeighted (s t q m n : ℕ) (g : ℕ → ℕ → ℤ)
    (u : ZMod s → GaussianInt) : List GaussianInt :=
  (List.range (3 * m + 1)).map fun a : ℕ =>
    tdivN q (u ((chirpStart s t m (n * m) + a : ℤ) : ZMod s) *
      (⟨g (n * m) a, 0⟩ : GaussianInt))

/-- The forward operand is exactly the aligned stream multiplier output on the
actual gathered window and its real coefficient table. -/
theorem chirpWeighted_eq_zipWith {s t q m n : ℕ} (hs : 0 < s) (hn : n * m < t)
    (g : ℕ → ℕ → ℤ) (u : ZMod s → GaussianInt) :
    chirpWeighted s t q m n g u =
      List.zipWith (fun x y => tdivN q (x * y)) (chirpWindow s t m n u)
        ((List.range (3 * m + 1)).map fun a : ℕ => (⟨g (n * m) a, 0⟩ : GaussianInt)) := by
  apply List.ext_getElem
  · simp [chirpWeighted, length_chirpWindow hs hn]
  · intro a ha hb
    have ha' : a < 3 * m + 1 := by simpa [chirpWeighted] using ha
    have hwin : a < (chirpWindow s t m n u).length := by
      rw [length_chirpWindow hs hn]; exact ha'
    have harg := chirpWindow_getD hs hn ha' u
    rw [List.getD_eq_getElem _ _ hwin] at harg
    simp only [chirpWeighted, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [harg]

/-- The convolution input reverses coefficients, preserving bits within each word. -/
def chirpOperandX (s t q m n : ℕ) (g : ℕ → ℕ → ℤ)
    (u : ZMod s → GaussianInt) : List GaussianInt :=
  (chirpWeighted s t q m n g u).reverse

/-- The kernel is shifted by `m-1`, with its factor one half supplied by precision. -/
def chirpOperandY (m n : ℕ) (k : ℕ → ℤ → ℤ) : List GaussianInt :=
  (List.range (4 * m)).map fun j : ℕ => ⟨k (n * m) ((j : ℤ) - (m - 1 : ℕ)), 0⟩

@[simp] theorem length_chirpOperandX (s t q m n : ℕ) (g : ℕ → ℕ → ℤ)
    (u : ZMod s → GaussianInt) : (chirpOperandX s t q m n g u).length = 3 * m + 1 := by
  simp [chirpOperandX, chirpWeighted]

@[simp] theorem length_chirpOperandY (m n : ℕ) (k : ℕ → ℤ → ℤ) :
    (chirpOperandY m n k).length = 4 * m := by simp [chirpOperandY]

/-- The total operand length gives exactly the existing `7m` no-wrap condition. -/
theorem chirpOperands_length (s t q m n l : ℕ) (g : ℕ → ℕ → ℤ)
    (k : ℕ → ℤ → ℤ) (u : ZMod s → GaussianInt) (hl : 7 * m ≤ 2 ^ l) :
    (chirpOperandX s t q m n g u).length + (chirpOperandY m n k).length ≤ 2 ^ l + 1 := by
  simp only [length_chirpOperandX, length_chirpOperandY]
  omega

/-- Every padded input coefficient has exactly the analytic ring-record value. -/
theorem value_chirpOperandX {s t : ℕ} [NeZero s] [NeZero t]
    (q m n i : ℕ) (g : ℕ → ℕ → ℤ) (u : ZMod s → GaussianInt) :
    value (q + 1) (block (chirpOperandX s t q m n g u) i) =
      chirpRecIn (t := t) m (rhoC q)
        (fun k0 a => (g k0 a : ℝ) / 2 ^ q) (fun j => value q (u j)) n i := by
  by_cases hi : i < 3 * m + 1
  · have hr : i < (chirpWeighted s t q m n g u).length := by
      simpa [chirpWeighted] using hi
    have ha : 3 * m - i < 3 * m + 1 := by omega
    change value (q + 1) ((chirpWeighted s t q m n g u).reverse.getD i 0) = _
    rw [List.getD_reverse i hr]
    simp only [chirpWeighted, List.length_map, List.length_range]
    rw [show 3 * m + 1 - 1 - i = 3 * m - i by omega]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_map, List.getElem_range, value_weighted,
      chirpRecIn, ite_eq_left hi, chirpIn, chirpStart_eq]
  · rw [block_eq_zero _ (by simpa using Nat.le_of_not_gt hi)]
    simp [value, chirpRecIn, hi, Complex.ext_iff]

/-- Every padded kernel coefficient has exactly the shifted analytic record value. -/
theorem value_chirpOperandY (q m n i : ℕ) (k : ℕ → ℤ → ℤ) :
    value (q + 1) (block (chirpOperandY m n k) i) =
      chirpRecK m (fun k0 a => (k k0 a : ℝ) / 2 ^ q) n i := by
  by_cases hi : i < 4 * m
  · change value (q + 1) ((chirpOperandY m n k).getD i 0) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [chirpOperandY, List.getElem_map, List.getElem_range,
      value_succ, value_real, chirpRecK, ite_eq_left hi]
  · rw [block_eq_zero _ (by simpa using Nat.le_of_not_gt hi)]
    simp [value, chirpRecK, hi, Complex.ext_iff]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
