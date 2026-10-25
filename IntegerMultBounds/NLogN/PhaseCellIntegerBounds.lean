module

public import IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

/-! # Product and partial-accumulator bounds for integer generator setup

Bounds apply to every sublist of the row terms, hence to every prefix or
suffix accumulation order. No generated arithmetic certificate is used.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

open ToeplitzInverse

/-- Integer products evaluated by one off-diagonal generator row. -/
def rowTerms (P s t u band L n i : ℕ) : List ℤ :=
  (List.range L).map (fun k => if k = i then 0 else coefficientNumerator P s t u band (gap i k) *
    (columnNumerators P s t u band L n).getD k 0)

@[simp] theorem rowTerms_length (P s t u band L n i : ℕ) :
    (rowTerms P s t u band L n i).length = L := by simp [rowTerms]

theorem rowTerms_sum (P s t u band L n i : ℕ) :
    (rowTerms P s t u band L n i).sum =
      generatorOffDiag (coefficientNumerator P s t u band) (columnNumerators P s t u band L n) i := by
  simp only [rowTerms, generatorOffDiag, columnNumerators_length]

theorem rowTerms_abs_le {P s t u band L n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (i : ℕ) :
    ∀ z ∈ rowTerms P s t u band L n i, |z| ≤ (2 : ℤ) ^ (P * (n + 1) + 1) := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
  have hkL : k < L := List.mem_range.mp hk
  by_cases hki : k = i
  · simp [hki]
  · simp only [hki, ite_false, abs_mul]
    calc
      _ ≤ (2 : ℤ) ^ P * (2 : ℤ) ^ (P * n + 1) :=
        mul_le_mul (coefficientNumerator_abs_le hP s t u band (gap i k))
          (columnNumerators_abs_le hP hs hst hu hn k hkL) (abs_nonneg _) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring

private theorem abs_sum_le_length_mul (xs : List ℤ) (B : ℤ)
    (hx : ∀ z ∈ xs, |z| ≤ B) : |xs.sum| ≤ (xs.length : ℤ) * B := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
      have hz := hx z (by simp)
      have ht := ih (fun y hy => hx y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact (abs_add_le _ _).trans (by nlinarith)

/-- Every partial sum fits a row-length logarithm beyond the product width. -/
theorem rowPartial_abs_le {P s t u band L n l : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (hL : L ≤ 2 ^ l) (i : ℕ)
    (xs : List ℤ) (hxs : xs.Sublist (rowTerms P s t u band L n i)) :
    |xs.sum| ≤ (2 : ℤ) ^ (P * (n + 1) + l + 1) := by
  have hh := abs_sum_le_length_mul xs ((2 : ℤ) ^ (P * (n + 1) + 1))
    (fun z hz => rowTerms_abs_le hP hs hst hu hn i z (hxs.subset hz))
  have hlen : xs.length ≤ L := by simpa only [rowTerms_length] using hxs.length_le
  have hlenZ : (xs.length : ℤ) ≤ (2 : ℤ) ^ l := by exact_mod_cast hlen.trans hL
  calc
    _ ≤ (xs.length : ℤ) * (2 : ℤ) ^ (P * (n + 1) + 1) := hh
    _ ≤ (2 : ℤ) ^ l * (2 : ℤ) ^ (P * (n + 1) + 1) :=
      mul_le_mul_of_nonneg_right hlenZ (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Subtracting any processed row fragment from the scaled unit RHS has one
additional guard bit. -/
theorem rowAccumulator_abs_le {P s t u band L n l : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (hL : L ≤ 2 ^ l) (i : ℕ)
    (xs : List ℤ) (hxs : xs.Sublist (rowTerms P s t u band L n i)) :
    |(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0) - xs.sum| ≤
      (2 : ℤ) ^ (P * (n + 1) + l + 2) := by
  have hsum := rowPartial_abs_le hP hs hst hu hn hL i xs hxs
  have hbase : |(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0)| ≤
      (2 : ℤ) ^ (P * (n + 1) + l + 1) := by
    split_ifs
    · simp only [mul_one, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (P * (n + 1)))]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    · simp
  calc
    _ ≤ |(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0)| + |xs.sum| := abs_sub _ _
    _ ≤ 2 * (2 : ℤ) ^ (P * (n + 1) + l + 1) := by omega
    _ = _ := by rw [show P * (n + 1) + l + 2 = (P * (n + 1) + l + 1) + 1 by omega, pow_succ]; ring

end IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
