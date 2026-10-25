module

public import IntegerMultBounds.NLogN.PhaseCellGeneratorData
public import IntegerMultBounds.NLogN.ToeplitzDyadicGenerator

/-! # Integer setup data for the actual phase-cell inverse column

The coefficient numerator uses the existing corrected exponential numerator.
The integer iteration recovers exactly the rational data already used by the
executed cell kernels; numerical accuracy therefore needs no new oracle.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

open ToeplitzInverse

/-- Integer numerator of the selected shared P-grid distance coefficient. -/
def coefficientNumerator (P s t u w k : ℕ) : ℤ :=
  if k = 0 then (2 : ℤ) ^ P else if k ≤ w then
    PhaseCellExpSample.numerator P (PhaseCellConcreteCoefficients.gaussianArg s t u k).aa
      (PhaseCellConcreteCoefficients.gaussianArg s t u k).b else 0

theorem coefficient_eq (P s t u w k : ℕ) :
    PhaseCellGeneratorData.coefficient P s t u w k =
      (coefficientNumerator P s t u w k : ℚ) / (2 : ℚ) ^ P := by
  simp [PhaseCellGeneratorData.coefficient, PhaseCellConcreteCoefficients.kernel,
    PhaseCellExecutableCoefficients.kernel, PhaseCellExecutableCoefficients.ExpArg.value,
    PhaseCellExpSample.sample, coefficientNumerator]
  split_ifs <;> simp_all

/-- Every selected distance-coefficient numerator is bounded by its P-grid
unit, including the exact diagonal and literal band truncation. -/
theorem coefficientNumerator_abs_le {P : ℕ} (hP : 13 ≤ P) (s t u w k : ℕ) :
    |coefficientNumerator P s t u w k| ≤ (2 : ℤ) ^ P := by
  unfold coefficientNumerator
  split_ifs with hk hband
  · simp
  · let arg := PhaseCellConcreteCoefficients.gaussianArg s t u k
    have hv := ((PhaseCellExecutableCoefficients.ExpArg.value_spec P arg hP).2.1).trans
      (PhaseCellExecutableCoefficients.ExpArg.target_bounds arg).2
    have hratio : ((PhaseCellExpSample.numerator P arg.aa arg.b : ℕ) : ℝ) / (2 : ℝ) ^ P ≤ 1 := by
      simpa only [PhaseCellExecutableCoefficients.ExpArg.value, PhaseCellExpSample.sample,
        Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using hv
    have hh := (div_le_one (by positivity : (0 : ℝ) < 2 ^ P)).mp hratio
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hh
  · simp

/-- No rational division is performed inside this finite integer recurrence. -/
def columnNumerators (P s t u w L n : ℕ) : List ℤ :=
  dyadicGeneratorIter P (coefficientNumerator P s t u w) (fun i => if i = 0 then 1 else 0) L n

@[simp] theorem columnNumerators_length (P s t u w L n : ℕ) :
    (columnNumerators P s t u w L n).length = L := by simp [columnNumerators]

theorem columnNumerators_spec (P s t u w L n : ℕ) :
    List.map (fun z : ℤ => (z : ℚ) / (2 : ℚ) ^ (P * n)) (columnNumerators P s t u w L n) =
      PhaseCellGeneratorData.column P s t u w L n := by
  have hh := dyadicGeneratorIter_spec P (coefficientNumerator P s t u w)
    (fun i => if i = 0 then 1 else 0) L n
  have hc : PhaseCellGeneratorData.coefficient P s t u w =
      (fun k => (coefficientNumerator P s t u w k : ℚ) / (2 : ℚ) ^ P) := by
    funext k
    exact coefficient_eq P s t u w k
  rw [← hc] at hh
  simpa only [columnNumerators, PhaseCellGeneratorData.column, Int.cast_ite,
    Int.cast_one, Int.cast_zero] using hh

/-- The first iteration is a scaled unit vector and needs no matrix product.
Subsequent setup steps therefore start in the positive-iteration bounds. -/
theorem columnNumerators_one (P s t u w L : ℕ) :
    columnNumerators P s t u w L 1 = (List.range L).map (fun i => if i = 0 then (2 : ℤ) ^ P else 0) := by
  simp [columnNumerators, dyadicGeneratorIter, generatorStep, generatorOffDiag, mul_ite]

/-- A stored integer entry decodes to the actual rational generator entry. -/
theorem columnNumerators_getD (P s t u w L n i : ℕ) :
    (((columnNumerators P s t u w L n).getD i 0 : ℤ) : ℚ) / (2 : ℚ) ^ (P * n) =
      (PhaseCellGeneratorData.column P s t u w L n).getD i 0 := by
  have hh := congrArg (fun xs : List ℚ => xs.getD i 0) (columnNumerators_spec P s t u w L n)
  have hget := List.getD_map (l := columnNumerators P s t u w L n) (d := (0 : ℤ))
    (fun z : ℤ => (z : ℚ) / (2 : ℚ) ^ (P * n)) (n := i)
  simp only [Int.cast_zero, zero_div] at hget
  exact hget.symm.trans hh

/-- The integer divisor used for reciprocal setup is strictly positive. -/
theorem columnNumerators_corner_pos {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    0 < (columnNumerators P s t u w L n).getD 0 0 := by
  have hcorner := PhaseCellGeneratorData.column_corner_lower (w := w) hP hs hst hu hL hn
  have hpositive : (0 : ℚ) < (PhaseCellGeneratorData.column P s t u w L n).getD 0 0 := by
    have hh : (0 : ℝ) < ((PhaseCellGeneratorData.column P s t u w L n).getD 0 0 : ℝ) := by linarith
    exact_mod_cast hh
  have hratio : (0 : ℚ) < (((columnNumerators P s t u w L n).getD 0 0 : ℤ) : ℚ) / (2 : ℚ) ^ (P * n) := by
    rw [columnNumerators_getD]
    exact hpositive
  have hnum := (div_pos_iff_of_pos_right (by positivity : (0 : ℚ) < 2 ^ (P * n))).mp hratio
  exact_mod_cast hnum

/-- A linear-in-iteration bit allowance bounds every stored integer column
entry. The bound does not grow with the number of rows. -/
theorem columnNumerators_abs_le {P s t u w L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (i : ℕ) (hi : i < L) :
    |(columnNumerators P s t u w L n).getD i 0| ≤ (2 : ℤ) ^ (P * n + 1) := by
  let z := (columnNumerators P s t u w L n).getD i 0
  have hread : (z : ℝ) / (2 : ℝ) ^ (P * n) =
      ((PhaseCellGeneratorData.column P s t u w L n).getD i 0 : ℝ) := by
    exact_mod_cast columnNumerators_getD P s t u w L n i
  have hcol := PhaseCellGeneratorData.column_abs_le (w := w) hP hs hst hu hn i hi
  rw [← hread, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (P * n))] at hcol
  have hnum := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (P * n))).mp hcol
  have hh : |(z : ℝ)| ≤ (2 : ℝ) ^ (P * n + 1) := by
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < 2 ^ (P * n) by positivity]
  exact_mod_cast hh

end IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
