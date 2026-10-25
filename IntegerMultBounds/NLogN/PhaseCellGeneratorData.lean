module

public import IntegerMultBounds.NLogN.ToeplitzGeneratorIteration
public import IntegerMultBounds.NLogN.PhaseCellToeplitz

/-! # Computable rational phase-cell inverse-generator data

The finite recurrence uses the corrected executable coefficient samples. Its
exact inverse appears only in the error statements. This is a numerical data
constructor, not yet a tape execution or fixed-width encoding theorem.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellGeneratorData

open Finset ToeplitzInverse

/-- Shared rational distance coefficients of the actual rounded cell matrix. -/
def coefficient (P s t u w : ℕ) (k : ℕ) : ℚ :=
  PhaseCellConcreteCoefficients.kernel P s t u w (k : ℤ)

/-- Approximate first inverse column, constructed by finite rational arithmetic. -/
def column (P s t u w L n : ℕ) : List ℚ :=
  generatorIter (coefficient P s t u w) id (fun k => if k = 0 then 1 else 0) L n

@[simp] theorem column_length (P s t u w L n : ℕ) :
    (column P s t u w L n).length = L := by simp [column]

/-- Accuracy against the first column of the actual selected matrix inverse. -/
theorem column_error {P s t u w L : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (n i : ℕ) (hi : i < L) :
    |((column P s t u w L n).getD i 0 : ℝ) -
      col (natInv L (PhaseCellToeplitz.coeff P s t u w)) i| ≤
      (1 / 8 : ℝ) ^ n / (1 - 1 / 8) := by
  have h := rationalGenerator_column_error (coefficient P s t u w)
    (by simp [coefficient, PhaseCellConcreteCoefficients.kernel])
    (PhaseCellToeplitz.rowMass hP hs hst hu L) (by norm_num) (by norm_num)
    0 (by omega) n i hi
  exact h

/-- Shifted reverse column used by the second Gohberg–Semencul branch. -/
def reversedColumn (P s t u w L n : ℕ) : List ℚ :=
  (List.range L).map (fun i => if i = 0 then 0 else (column P s t u w L n).getD (L - i) 0)

@[simp] theorem reversedColumn_length (P s t u w L n : ℕ) :
    (reversedColumn P s t u w L n).length = L := by simp [reversedColumn]

theorem reversedColumn_error {P s t u w L : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (n i : ℕ) (hi : i < L) :
    |((reversedColumn P s t u w L n).getD i 0 : ℝ) -
      rev L (natInv L (PhaseCellToeplitz.coeff P s t u w)) i| ≤
      (1 / 8 : ℝ) ^ n / (1 - 1 / 8) := by
  have hget : (reversedColumn P s t u w L n).getD i 0 =
      if i = 0 then 0 else (column P s t u w L n).getD (L - i) 0 := by
    simp [reversedColumn, List.getD, hi]
  rw [hget]
  cases i with
  | zero => simp [rev]; positivity
  | succ i =>
    have hr := rev_eq (isInverse (g := PhaseCellToeplitz.coeff P s t u w)
      PhaseCellToeplitz.coeff_zero (PhaseCellToeplitz.rowMass hP hs hst hu L) (by norm_num))
      i (by omega)
    rw [hr]
    simpa only [Nat.add_one_ne_zero, ite_false, show L - (i + 1) = L - 1 - i by omega] using
      column_error (w := w) (L := L) hP hs hst hu n (L - 1 - i) (by omega)

/-- One or more iterations suffice to keep the computed corner uniformly away
from zero. The reciprocal can therefore be constructed by rational division. -/
theorem column_corner_lower {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    (5 / 7 : ℝ) ≤ ((column P s t u w L n).getD 0 0 : ℝ) := by
  have he := column_error (w := w) (L := L) hP hs hst hu n 0 hL
  have hx := (PhaseCellToeplitz.block_inverse (w := w) hP hs hst hu L hL).2.1
  have hp : (1 / 8 : ℝ) ^ n ≤ 1 / 8 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) hn
  have herr : (1 / 8 : ℝ) ^ n / (1 - 1 / 8) ≤ 1 / 7 := by
    norm_num at *
    linarith
  have hl := (abs_le.mp he).1
  unfold col at hl
  linarith

/-- Computed generator entries fit within the scale-two normalization with
uniform slack, independent of the cell length. -/
theorem column_abs_le {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (i : ℕ) (hi : i < L) :
    |((column P s t u w L n).getD i 0 : ℝ)| ≤ 3 / 2 := by
  have he := column_error (w := w) (L := L) hP hs hst hu n i hi
  have hp : (1 / 8 : ℝ) ^ n ≤ 1 / 8 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) hn
  have herr : (1 / 8 : ℝ) ^ n / (1 - 1 / 8) ≤ 1 / 7 := by
    norm_num at *
    linarith
  have hrow := row_abs_sum (g := PhaseCellToeplitz.coeff P s t u w)
    PhaseCellToeplitz.coeff_zero (PhaseCellToeplitz.rowMass hP hs hst hu L) (by norm_num) i hi
  have hv := (single_le_sum (f := fun k => |natInv L (PhaseCellToeplitz.coeff P s t u w) i k|)
    (fun _ _ => abs_nonneg _) (mem_range.mpr (show 0 < L by omega))).trans hrow
  have ht := abs_add_le (((column P s t u w L n).getD i 0 : ℝ) -
    col (natInv L (PhaseCellToeplitz.coeff P s t u w)) i)
    (col (natInv L (PhaseCellToeplitz.coeff P s t u w)) i)
  rw [sub_add_cancel] at ht
  unfold col at *
  norm_num at hv
  linarith

theorem reversedColumn_abs_le {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (i : ℕ) (hi : i < L) :
    |((reversedColumn P s t u w L n).getD i 0 : ℝ)| ≤ 3 / 2 := by
  have hget : (reversedColumn P s t u w L n).getD i 0 =
      if i = 0 then 0 else (column P s t u w L n).getD (L - i) 0 := by
    simp [reversedColumn, List.getD, hi]
  rw [hget]
  by_cases hi0 : i = 0
  · norm_num [hi0]
  · simp only [if_neg hi0]
    exact column_abs_le (w := w) (L := L) hP hs hst hu hn (L - i) (by omega)

/-- Reciprocal of the computed corner; no exact inverse is used by this definition. -/
def reciprocal (P s t u w L n : ℕ) : ℚ :=
  1 / (column P s t u w L n).getD 0 0

/-- The stored scalar's required norm bound follows from construction. -/
theorem reciprocal_bounds {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    0 < (reciprocal P s t u w L n : ℝ) ∧ (reciprocal P s t u w L n : ℝ) ≤ 2 := by
  have hc := column_corner_lower (w := w) hP hs hst hu hL hn
  have hc0 : (0 : ℝ) < ((column P s t u w L n).getD 0 0 : ℝ) := by linarith
  simp only [reciprocal, Rat.cast_div, Rat.cast_one]
  constructor
  · positivity
  · apply (div_le_iff₀ hc0).mpr
    linarith

/-- Rational division of the computed corner approximates the inverse corner
reciprocal, with no more than twice the column error. -/
theorem reciprocal_error {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    |(reciprocal P s t u w L n : ℝ) -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u w) 0 0| ≤
      2 * ((1 / 8 : ℝ) ^ n / (1 - 1 / 8)) := by
  let a : ℝ := (column P s t u w L n).getD 0 0
  let b := natInv L (PhaseCellToeplitz.coeff P s t u w) 0 0
  let ε := (1 / 8 : ℝ) ^ n / (1 - 1 / 8)
  have ha : 5 / 7 ≤ a := column_corner_lower (w := w) hP hs hst hu hL hn
  have hb : 6 / 7 ≤ b := (PhaseCellToeplitz.block_inverse (w := w) hP hs hst hu L hL).2.1
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have he : |a - b| ≤ ε := column_error (w := w) (L := L) hP hs hst hu n 0 hL
  have he0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hab : 1 ≤ 2 * (a * b) := by nlinarith [mul_le_mul ha hb (by norm_num) ha0.le]
  have heq : 1 / a - 1 / b = -(a - b) / (a * b) := by
    field_simp
    <;> ring
  simp only [reciprocal, Rat.cast_div, Rat.cast_one]
  change |1 / a - 1 / b| ≤ 2 * ε
  rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos ha0 hb0)]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).mpr
  have h := mul_le_mul_of_nonneg_right hab he0
  nlinarith

/-- A linear iteration count pays for both generator and reciprocal accuracy. -/
theorem iteration_error_precision (j : ℕ) :
    2 * ((1 / 8 : ℝ) ^ (j + 1) / (1 - 1 / 8)) ≤ 1 / (2 : ℝ) ^ j := by
  have hp : (1 / 8 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := by gcongr <;> norm_num
  have hp0 : 0 ≤ (1 / 8 : ℝ) ^ j := by positivity
  calc
    _ = (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ j := by rw [pow_succ]; ring
    _ ≤ (1 / 2 : ℝ) ^ j := by linarith
    _ = 1 / (2 : ℝ) ^ j := by rw [one_div_pow]

theorem column_error_precision {P s t u w L : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (j i : ℕ) (hi : i < L) :
    |((column P s t u w L (j + 1)).getD i 0 : ℝ) -
      col (natInv L (PhaseCellToeplitz.coeff P s t u w)) i| ≤ 1 / (2 : ℝ) ^ j := by
  have h := column_error (w := w) (L := L) hP hs hst hu (j + 1) i hi
  have he0 : 0 ≤ (1 / 8 : ℝ) ^ (j + 1) / (1 - 1 / 8) := by positivity
  exact h.trans ((by linarith :
    (1 / 8 : ℝ) ^ (j + 1) / (1 - 1 / 8) ≤ 2 * ((1 / 8 : ℝ) ^ (j + 1) / (1 - 1 / 8))).trans
      (iteration_error_precision j))

theorem reciprocal_error_precision {P s t u w L : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (j : ℕ) :
    |(reciprocal P s t u w L (j + 1) : ℝ) -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u w) 0 0| ≤ 1 / (2 : ℝ) ^ j :=
  (reciprocal_error (w := w) (n := j + 1) hP hs hst hu hL (by omega)).trans
    (iteration_error_precision j)

end IntegerMultBounds.NLogN.PhaseCellGeneratorData
