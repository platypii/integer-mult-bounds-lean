module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators
public import IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

/-! # Inverse-generator encoding by integer arithmetic

The actual column words are obtained from the integer recurrence by a signed
integer quotient. No rational floor or supplied inverse data is needed in this
representation; tape execution and its width/cost proof remain separate.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- Exact downward q-grid encoding of a signed dyadic numerator. -/
def dyadicWord (q r : ℕ) (z : ℤ) : GaussianInt :=
  ⟨((2 : ℤ) ^ q * z) / ((2 : ℕ) ^ r : ℤ), 0⟩

theorem dyadicWord_eq (q r : ℕ) (z : ℤ) :
    dyadicWord q r z = rationalWord q ((z : ℚ) / (2 : ℚ) ^ r) := by
  unfold dyadicWord rationalWord
  congr 1
  have hh := Rat.floor_intCast_div_natCast ((2 : ℤ) ^ q * z) ((2 : ℕ) ^ r)
  push_cast at hh
  simpa only [mul_div_assoc, Nat.cast_ofNat] using hh.symm

def integerColumnWords (P s t u band L q n : ℕ) : List GaussianInt :=
  List.map (dyadicWord q (P * n + 1)) (PhaseCellIntegerGenerators.columnNumerators P s t u band L n)

/-- Integer-only encoding agrees exactly with the words consumed by the
complete cell execution theorem. -/
theorem integerColumnWords_eq (P s t u band L q n : ℕ) :
    integerColumnWords P s t u band L q n = columnWords P s t u band L q n := by
  unfold integerColumnWords columnWords normalizedWords
  rw [← PhaseCellIntegerGenerators.columnNumerators_spec]
  rw [List.map_map]
  apply List.map_congr_left
  intro z _
  rw [dyadicWord_eq]
  simp only [Function.comp_apply]
  congr 1
  rw [pow_succ]
  ring

/-- The second branch's shifted reverse uses the same stored integer column. -/
def integerReversedColumnWords (P s t u band L q n : ℕ) : List GaussianInt :=
  (List.range L).map (fun i => if i = 0 then 0 else
    dyadicWord q (P * n + 1)
      ((PhaseCellIntegerGenerators.columnNumerators P s t u band L n).getD (L - i) 0))

theorem integerReversedColumnWords_eq (P s t u band L q n : ℕ) :
    integerReversedColumnWords P s t u band L q n = reversedColumnWords P s t u band L q n := by
  unfold integerReversedColumnWords reversedColumnWords normalizedWords PhaseCellGeneratorData.reversedColumn
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  by_cases hi : i = 0
  · simp [hi, rationalWord]; rfl
  · simp only [hi, ite_false]
    rw [dyadicWord_eq, ← PhaseCellIntegerGenerators.columnNumerators_getD]
    congr 1
    rw [pow_succ]
    ring

/-- The stored reciprocal is one integer division by the positive corner. -/
def integerReciprocalWord (P s t u band L q n : ℕ) : GaussianInt :=
  ⟨(2 : ℤ) ^ (q + P * n) / (PhaseCellIntegerGenerators.columnNumerators P s t u band L n).getD 0 0, 0⟩

theorem integerReciprocalWord_eq {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    integerReciprocalWord P s t u band L q n = reciprocalWord P s t u band L q n := by
  let corner := (PhaseCellIntegerGenerators.columnNumerators P s t u band L n).getD 0 0
  have hcorner : 0 < corner := PhaseCellIntegerGenerators.columnNumerators_corner_pos hP hs hst hu hL hn
  have hden : (corner.toNat : ℤ) = corner := Int.toNat_of_nonneg hcorner.le
  have hdenQ : (corner.toNat : ℚ) = (corner : ℚ) := by exact_mod_cast hden
  have hfloor := Rat.floor_intCast_div_natCast ((2 : ℤ) ^ (q + P * n)) corner.toNat
  push_cast at hfloor
  rw [hden, hdenQ] at hfloor
  unfold integerReciprocalWord reciprocalWord PhaseCellGeneratorData.reciprocal rationalWord
  rw [← PhaseCellIntegerGenerators.columnNumerators_getD]
  change (⟨(2 : ℤ) ^ (q + P * n) / corner, 0⟩ : GaussianInt) =
    ⟨⌊(2 : ℚ) ^ q * (1 / ((corner : ℚ) / (2 : ℚ) ^ (P * n)))⌋, 0⟩
  congr 1
  rw [← hfloor]
  congr 1
  rw [pow_add]
  field_simp

/-- Stored inverse-column integers fit a setup word whose width grows only
linearly with the coefficient precision times the iteration count. -/
theorem columnNumerator_fits {P s t u band L n W : ℕ} (hW : P * n + 3 ≤ W)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (i : ℕ) (hi : i < L) :
    Fits W (⟨(PhaseCellIntegerGenerators.columnNumerators P s t u band L n).getD i 0, 0⟩ : GaussianInt) := by
  constructor
  · exact (PhaseCellIntegerGenerators.columnNumerators_abs_le hP hs hst hu hn i hi).trans_lt
      (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (by omega))
  · change |(0 : ℤ)| < (2 : ℤ) ^ (W - 1)
    simpa only [abs_zero] using pow_pos (by norm_num : (0 : ℤ) < 2) (W - 1)

/-- The numerator passed to reciprocal division has an explicit setup width. -/
theorem reciprocalNumerator_fits {P q n W : ℕ} (hW : q + P * n + 2 ≤ W) :
    Fits W (⟨(2 : ℤ) ^ (q + P * n), 0⟩ : GaussianInt) := by
  constructor
  · change |(2 : ℤ) ^ (q + P * n)| < (2 : ℤ) ^ (W - 1)
    rw [abs_of_pos (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  · change |(0 : ℤ)| < (2 : ℤ) ^ (W - 1)
    simpa only [abs_zero] using pow_pos (by norm_num : (0 : ℤ) < 2) (W - 1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
