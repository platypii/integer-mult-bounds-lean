module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowTable
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators

/-! # Data produced by the executed input, interior and final-weight stages

These constructors use the exact truncated products of the verified machines.
Their bank-to-bank arithmetic composition is proved in `PhaseCellConstructedExecution`.
Setup generation remains separate; no equality with the rational-floor reference is asserted.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def cellSourceRows {s : ℕ} (L : ℕ) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (n : ℕ) : List GaussianInt :=
  (List.range L).map (fun k : ℕ => C n (lo n + (k : ZMod s)))

def cellWeightRows (s t p u L : ℕ) (lo : ℕ → ZMod s) (n : ℕ) : List ℚ :=
  (List.range L).map (fun k => weightData s t p u (lo n) k)

@[simp] theorem cellSourceRows_length {s : ℕ} (L : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n : ℕ) : (cellSourceRows L lo C n).length = L := by simp [cellSourceRows]

@[simp] theorem cellWeightRows_length (s t p u L : ℕ) (lo : ℕ → ZMod s) (n : ℕ) :
    (cellWeightRows s t p u L lo n).length = L := by simp [cellWeightRows]

theorem cellSourceRows_getD {s : ℕ} (L : ℕ) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (n i : ℕ) (hi : i < L) : (cellSourceRows L lo C n).getD i 0 = C n (lo n + (i : ZMod s)) := by
  simp [cellSourceRows, List.getD, hi]

theorem cellWeightRows_getD (s t p u L : ℕ) (lo : ℕ → ZMod s) (n i : ℕ) (hi : i < L) :
    (cellWeightRows s t p u L lo n).getD i 0 = weightData s t p u (lo n) i := by
  simp [cellWeightRows, List.getD, hi]

theorem cellWeightRows_bounds {s t p u L : ℕ} {α d : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (lo : ℕ → ZMod s) (n : ℕ) :
    ∀ a ∈ cellWeightRows s t p u L lo n,
      1 / (2 : ℝ) ^ (8 * p + 1) ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1 := by
  intro a ha
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
  exact weightData_bounds hp hs hαu hθ hgap hbudget (lo n) k

def executedInputRows (s t p u q L cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n : ℕ) : List GaussianInt :=
  weightedInputNumerators q cExp (8 * p + 1) (cellSourceRows L lo C n) (cellWeightRows s t p u L lo n)

@[simp] theorem executedInputRows_length (s t p u q L cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n : ℕ) : (executedInputRows s t p u q L cExp lo C n).length = L := by
  simp [executedInputRows, weightedInputNumerators, reciprocalWeightWords, cellSourceRows, cellWeightRows]

theorem executedInputRows_disk {s t p u q L cExp M : ℕ} {α d : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value q (C n k)‖ ≤ (2 : ℝ) ^ cExp) :
    ∀ n < M, ∀ z ∈ executedInputRows s t p u q L cExp lo C n,
      z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  intro n hn
  apply weightedInputNumerators_disk
  · intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hC n hn _
  · intro a ha
    exact (cellWeightRows_bounds hp hs hαu hθ hgap hbudget lo n a ha).1

theorem executedInputRows_error {s t p u q L cExp j : ℕ}
    (hq : inputExponent p cExp + j + 1 ≤ q) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n i : ℕ) (hi : i < L) :
    |(2 : ℝ) ^ inputExponent p cExp * (value q (block (executedInputRows s t p u q L cExp lo C n) i)).re -
      (value q (C n (lo n + (i : ZMod s)))).re *
        (value q (reciprocalWeightWord q (weightData s t p u (lo n) i))).re| ≤ 1 / (2 : ℝ) ^ j := by
  have hsrc : i < (cellSourceRows L lo C n).length := by simpa using hi
  have hds : i < (cellWeightRows s t p u L lo n).length := by simpa using hi
  have hsource : (cellSourceRows L lo C n)[i] = C n (lo n + (i : ZMod s)) := by
    simpa only [List.getD_eq_getElem _ _ hsrc] using cellSourceRows_getD L lo C n i hi
  have hweight : (cellWeightRows s t p u L lo n)[i] = weightData s t p u (lo n) i := by
    simpa only [List.getD_eq_getElem _ _ hds] using cellWeightRows_getD s t p u L lo n i hi
  have h := weightedInputNumerators_error_precision (q := q) (cExp := cExp) (e := 8 * p + 1) (j := j)
    hq (cellSourceRows L lo C n) (cellWeightRows s t p u L lo n) (by simp) i hsrc
  simpa only [inputExponent, executedInputRows, hsource, hweight] using h

/-- The scalar stream emitted by the actual four-product interior program. -/
def executedInteriorWords (s t p u q l M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) : List GaussianInt :=
  (branchDifference q l M L
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (executedInputRows s t p u q L cExp lo C)).map
    (fun x => tdivN q (x * reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)))

@[simp] theorem executedInteriorWords_length (s t p u q l M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) : (executedInteriorWords s t p u q l M L j cExp lo C).length = M * L := by
  simp [executedInteriorWords, branchDifference]

theorem executedInteriorWords_norm {s t p u q l M L j cExp : ℕ} {α d : ℝ}
    (hp : 0 < p) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hq : 2 ≤ q)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value q (C n k)‖ ≤ (2 : ℝ) ^ cExp) :
    ∀ z ∈ executedInteriorWords s t p u q l M L j cExp lo C, ‖value q z‖ ≤ 4 := by
  have hprecision : 13 ≤ 2 ^ 15 * p := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  apply scalar_products_norm
  · apply branchDifference_norm hpad
    · intro n hn; simp
    · intro n hn; simp
    · intro n hn; simp
    · intro n hn; exact columnWords_disk hprecision hs hst hu hq (by omega)
    · intro n hn; exact reversedColumnWords_disk hprecision hs hst hu hq (by omega)
    · exact executedInputRows_disk hp hs hαu hθ hgap hbudget lo C hC
  · exact reciprocalWord_norm hprecision hs hst hu hL (by omega)

/-- Final weights use the actual reversed coordinate order of the compact rows. -/
def executedOutputTable (s t p u M L : ℕ) (lo : ℕ → ZMod s) : List ℚ :=
  reversedRowTable M L (fun n i => weightData s t p u (lo n) i)

/-- The list emitted by the actual final shift and aligned weight multiplication. -/
def executedOutputWords (s t p u q l M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) : List GaussianInt :=
  weightedOutputNumerators q (inputExponent p cExp + 2 * l + 2)
    (executedInteriorWords s t p u q l M L j cExp lo C) (executedOutputTable s t p u M L lo)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
