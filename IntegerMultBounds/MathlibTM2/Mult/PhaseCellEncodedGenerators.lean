module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorWords

/-! # Encoded inverse generators and reciprocal for the executed cell kernel

The constructors produce real Gaussian words from rational setup data. Their
range lemmas discharge the raw operand disk and scalar norm hypotheses of the
interior execution theorem. Generating these words on tape remains open.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse

/-- The first generator is stored at scale two. -/
def columnWords (P s t u band L q n : ℕ) : List GaussianInt :=
  normalizedWords q (PhaseCellGeneratorData.column P s t u band L n)

/-- The second generator uses the same encoding and its shifted reverse data. -/
def reversedColumnWords (P s t u band L q n : ℕ) : List GaussianInt :=
  normalizedWords q (PhaseCellGeneratorData.reversedColumn P s t u band L n)

/-- The reciprocal is stored at its actual scale. -/
def reciprocalWord (P s t u band L q n : ℕ) : GaussianInt :=
  rationalWord q (PhaseCellGeneratorData.reciprocal P s t u band L n)

@[simp] theorem columnWords_length (P s t u band L q n : ℕ) :
    (columnWords P s t u band L q n).length = L := by simp [columnWords]

@[simp] theorem reversedColumnWords_length (P s t u band L q n : ℕ) :
    (reversedColumnWords P s t u band L q n).length = L := by simp [reversedColumnWords]

theorem columnWords_disk {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∀ z ∈ columnWords P s t u band L q n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  apply normalizedWords_disk hq
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have h := PhaseCellGeneratorData.column_abs_le (w := band) (L := L) hP hs hst hu hn i
    (by simpa using hi)
  simpa only [List.getD_eq_getElem _ _ hi] using h

theorem reversedColumnWords_disk {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∀ z ∈ reversedColumnWords P s t u band L q n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  apply normalizedWords_disk hq
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have h := PhaseCellGeneratorData.reversedColumn_abs_le (w := band) (L := L) hP hs hst hu hn i
    (by simpa using hi)
  simpa only [List.getD_eq_getElem _ _ hi] using h

theorem reciprocalWord_norm {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    ‖value q (reciprocalWord P s t u band L q n)‖ ≤ 2 := by
  have hr := PhaseCellGeneratorData.reciprocal_bounds (w := band) hP hs hst hu hL hn
  have hrQ : 0 ≤ PhaseCellGeneratorData.reciprocal P s t u band L n := by exact_mod_cast hr.1.le
  unfold reciprocalWord
  rw [rationalWord_norm, abs_of_nonneg (rationalWord_nonneg q _ hrQ)]
  exact (rationalWord_bounds q _).1.trans hr.2

/-- Encoding and finite-iteration errors add before any triangular stage. -/
theorem columnWords_error {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (i : ℕ) (hi : i < L) :
    |2 * (value q (block (columnWords P s t u band L q n) i)).re -
      col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤
      2 / (2 : ℝ) ^ q + (1 / 8 : ℝ) ^ n / (1 - 1 / 8) := by
  have he := normalizedWords_error q (PhaseCellGeneratorData.column P s t u band L n) i
  have hi' := PhaseCellGeneratorData.column_error (w := band) (L := L) hP hs hst hu n i hi
  exact (abs_sub_le _ _ _).trans (add_le_add he hi')

theorem reversedColumnWords_error {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (i : ℕ) (hi : i < L) :
    |2 * (value q (block (reversedColumnWords P s t u band L q n) i)).re -
      rev L (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤
      2 / (2 : ℝ) ^ q + (1 / 8 : ℝ) ^ n / (1 - 1 / 8) := by
  have he := normalizedWords_error q (PhaseCellGeneratorData.reversedColumn P s t u band L n) i
  have hi' := PhaseCellGeneratorData.reversedColumn_error (w := band) (L := L) hP hs hst hu n i hi
  exact (abs_sub_le _ _ _).trans (add_le_add he hi')

theorem reciprocalWord_error {P s t u band L q n : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hn : 1 ≤ n) :
    |(value q (reciprocalWord P s t u band L q n)).re -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u band) 0 0| ≤
      1 / (2 : ℝ) ^ q + 2 * ((1 / 8 : ℝ) ^ n / (1 - 1 / 8)) := by
  have he := rationalWord_error q (PhaseCellGeneratorData.reciprocal P s t u band L n)
  have hi' := PhaseCellGeneratorData.reciprocal_error (w := band) (n := n) hP hs hst hu hL hn
  exact (abs_sub_le _ _ _).trans (add_le_add he hi')

/-- Generator words are real, as required by the real triangular-stage proofs. -/
theorem normalizedWords_real (q : ℕ) (xs : List ℚ) :
    ∀ z ∈ normalizedWords q xs, z.im = 0 := by
  intro z hz
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz
  rfl

/-- One choice of grid precision and iteration count pays for both generator
and reciprocal setup errors. The two precisions retain separate meanings. -/
theorem encoded_setup_precision {j q : ℕ} (hq : j + 2 ≤ q) :
    (2 / (2 : ℝ) ^ q + (1 / 8 : ℝ) ^ (j + 2) / (1 - 1 / 8) ≤ 1 / (2 : ℝ) ^ j) ∧
    (1 / (2 : ℝ) ^ q + 2 * ((1 / 8 : ℝ) ^ (j + 2) / (1 - 1 / 8)) ≤ 1 / (2 : ℝ) ^ j) := by
  have hp : (2 : ℝ) ^ (j + 2) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hg : 2 / (2 : ℝ) ^ q ≤ 1 / (2 : ℝ) ^ (j + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have heq : (2 : ℝ) * 2 ^ (j + 1) = 2 ^ (j + 2) := by rw [pow_succ]; ring
    simpa only [heq, one_mul] using hp
  have he := PhaseCellGeneratorData.iteration_error_precision (j + 1)
  have hs : 2 * (1 / (2 : ℝ) ^ (j + 1)) = 1 / (2 : ℝ) ^ j := by
    rw [pow_succ]
    field_simp
  have hE : 0 ≤ (1 / 8 : ℝ) ^ (j + 2) / (1 - 1 / 8) := by positivity
  have hG : 0 ≤ 1 / (2 : ℝ) ^ q := by positivity
  have hg' : 2 * (1 / (2 : ℝ) ^ q) ≤ 1 / (2 : ℝ) ^ (j + 1) := by
    simpa only [mul_one_div] using hg
  constructor <;> linarith

theorem columnWords_error_precision {P s t u band L q j : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hq : j + 2 ≤ q) (i : ℕ) (hi : i < L) :
    |2 * (value q (block (columnWords P s t u band L q (j + 2)) i)).re -
      col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j :=
  (columnWords_error (band := band) (q := q) (n := j + 2) hP hs hst hu i hi).trans
    (encoded_setup_precision hq).1

theorem reversedColumnWords_error_precision {P s t u band L q j : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hq : j + 2 ≤ q) (i : ℕ) (hi : i < L) :
    |2 * (value q (block (reversedColumnWords P s t u band L q (j + 2)) i)).re -
      rev L (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j :=
  (reversedColumnWords_error (band := band) (q := q) (n := j + 2) hP hs hst hu i hi).trans
    (encoded_setup_precision hq).1

theorem reciprocalWord_error_precision {P s t u band L q j : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u) (hq : j + 2 ≤ q) (hL : 0 < L) :
    |(value q (reciprocalWord P s t u band L q (j + 2))).re -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u band) 0 0| ≤ 1 / (2 : ℝ) ^ j :=
  (reciprocalWord_error (band := band) (q := q) (n := j + 2) hP hs hst hu hL (by omega)).trans
    (encoded_setup_precision hq).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
