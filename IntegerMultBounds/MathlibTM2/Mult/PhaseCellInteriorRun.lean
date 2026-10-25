module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageValues
public import IntegerMultBounds.NLogN.PhaseCellRoundedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators

/-! # Cell runs interpreted from the executed interior arithmetic

The four triangular stages and merge are the computed S1/scalar numerators,
with the actual ring and magnitude scales. Reciprocal-weight construction,
input scaling and final weight multiplication remain explicit pending stages.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.ToeplitzInverse IntegerMultBounds.Spec.SignedRingProduct

/-- A real cell output read from its actual reversed-row tape position. -/
noncomputable def cellOutputValue {A : ℕ} (q l w L : ℕ) (B : ℝ) (n : ℕ)
    (tape : List (Fin (A + 4))) (i : ℕ) : ℝ :=
  4 * B * (2 ^ l : ℕ) ^ 2 *
    (value q (decodeWord ((tape.drop ((n * L + (L - 1 - i)) * w)).take w))).re

/-- Computed arrays for one row of the interior batch. -/
noncomputable def interiorRun {A : ℕ} (q l w M L : ℕ) (B : ℝ)
    (X Z V : ℕ → List GaussianInt) (a : GaussianInt) (n : ℕ)
    (r y : ℕ → ℝ) (tape : List (Fin (A + 4))) : PhaseCellMatrix.CellRun where
  r := r
  v := fun k => B * (value q (block (V n) k)).re
  xh := fun k => 2 * (value q (block (X n) k)).re
  zh := fun k => 2 * (value q (block (Z n) k)).re
  w := (value q a).re
  u₁ := fun k => (scaledUpper 2 (B : ℂ) q l L X V n k).re
  u₂ := fun k => 4 * B * (2 ^ l : ℕ) ^ 2 *
    (value q (block (pairRows q l M L X V) (n * L + (L - 1 - k)))).re
  u₃ := fun k => (scaledUpper 2 (B : ℂ) q l L Z V n k).re
  u₄ := fun k => 4 * B * (2 ^ l : ℕ) ^ 2 *
    (value q (block (pairRows q l M L Z V) (n * L + (L - 1 - k)))).re
  out := cellOutputValue q l w L B n tape
  y := y

private theorem input_real_bound {q : ℕ} (xs : List GaussianInt)
    (hxs : ∀ z ∈ xs, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (i : ℕ) (hi : i < xs.length) : |(value q (block xs i)).re| ≤ 1 := by
  have hz := hxs xs[i] (List.getElem_mem hi)
  have hd : DiskGrid q (fun _ : Fin 1 => xs[i].re) (fun _ => xs[i].im) := fun _ => hz
  have hn := hd.norm_le 0
  have hr := (Complex.abs_re_le_norm (value q xs[i])).trans hn
  simpa only [block, List.getElem?_eq_getElem hi, Option.getD_some, value, gridPoly] using hr

/-- Given generator accuracy, the computed arithmetic discharges the interior
stage clauses of the cell-run contract. Reciprocal-weight, input-scaling and
final-output stages remain pending; no triangular or merge oracle occurs. -/
theorem interiorRun_valid {A q l w M L s t p u : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw : q + 4 ≤ w) (B η : ℝ) (hB : 0 ≤ B)
    (hpad : L + L ≤ 2 ^ l + 1) (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hrealX : ∀ n < M, ∀ z ∈ X n, z.im = 0)
    (hrealZ : ∀ n < M, ∀ z ∈ Z n, z.im = 0)
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (hupper : 4 * B * (2 ^ l : ℕ) / (2 : ℝ) ^ q ≤ η)
    (hlower : 8 * B * (2 ^ l : ℕ) ^ 2 / (2 : ℝ) ^ q ≤ η)
    (n : Fin M) (lo : ZMod s) (c : ZMod s → ℝ) (r y : ℕ → ℝ)
    (tail tape : List (Fin (A + 4)))
    (htape : tape = cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)
    (hxh : ∀ i < L, |2 * (value q (block (X n) i)).re - col (natInv L
      (PhaseCellToeplitz.coeff (2 ^ 15 * p) s t u (PhaseCellBand.width p u))) i| ≤ η)
    (hzh : ∀ i < L, |2 * (value q (block (Z n) i)).re - rev L (natInv L
      (PhaseCellToeplitz.coeff (2 ^ 15 * p) s t u (PhaseCellBand.width p u))) i| ≤ η)
    (haerr : |(value q a).re - 1 / natInv L
      (PhaseCellToeplitz.coeff (2 ^ 15 * p) s t u (PhaseCellBand.width p u)) 0 0| ≤ η)
    (hr : ∀ k < L, |r k - 1 / PhaseCellMatrix.weight s t p u lo k| ≤ η)
    (hv : ∀ k < L, |B * (value q (block (V n) k)).re - c (lo + (k : ZMod s)) * r k| ≤ η)
    (hy : ∀ k < L, |y k - PhaseCellMatrix.weight s t p u lo k * cellOutputValue q l w L B n tape k| ≤ η) :
    (interiorRun q l w M L B X Z V a n r y tape).Valid s t p u lo L c η B := by
  refine ⟨hr, hv, ?_, ?_, ?_, haerr, ?_, ?_, ?_, ?_, ?_, hy⟩
  · intro i hi
    change |B * (value q (block (V n) i)).re| ≤ B
    rw [abs_mul, abs_of_nonneg hB]
    have h := input_real_bound (V n) (hV n n.isLt) i (by rw [hlenV n n.isLt]; exact Finset.mem_range.mp hi)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hB
  · intro i hi
    exact hxh i (Finset.mem_range.mp hi)
  · intro i hi
    exact hzh i (Finset.mem_range.mp hi)
  · intro i hi
    exact (upperNumerator_real_error B hB hpad X V hlenX hlenV hrealX n
      ⟨i, Finset.mem_range.mp hi⟩).trans hupper
  · intro i hi
    exact (pairNumerator_real_error B hB hpad X V hlenX hlenV hX hV hrealX n
      ⟨i, Finset.mem_range.mp hi⟩).trans hlower
  · intro i hi
    exact (upperNumerator_real_error B hB hpad Z V hlenZ hlenV hrealZ n
      ⟨i, Finset.mem_range.mp hi⟩).trans hupper
  · intro i hi
    exact (pairNumerator_real_error B hB hpad Z V hlenZ hlenV hZ hV hrealZ n
      ⟨i, Finset.mem_range.mp hi⟩).trans hlower
  · intro i hi
    have h := branchScalar_real_error hA hw B hB hpad X Z V hlenX hlenZ hlenV hX hZ hV
      a ha har tail (cellIndex n ⟨i, Finset.mem_range.mp hi⟩)
    simpa only [interiorRun, cellOutputValue, htape, pairNumerator, cellIndex] using h.trans hlower

/-- The cell run whose generator words come from the selected matrix's
computable setup constructors. -/
noncomputable def preparedRun {A : ℕ} (s t p u q l w M L j : ℕ) (B : ℝ)
    (V : ℕ → List GaussianInt) (n : ℕ) (r y : ℕ → ℝ) (tape : List (Fin (A + 4))) :
    PhaseCellMatrix.CellRun :=
  interiorRun q l w M L B
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    V (reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)) n r y tape

/-- Constructed generators and a common precision discharge all interior
arithmetic and setup-accuracy obligations. The three weight-related stages
remain explicit hypotheses awaiting their tape implementations. -/
theorem preparedRun_valid {A q l w M L s t p u j b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw : q + 4 ≤ w) (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (B : ℝ) (hB : 0 ≤ B) (hBb : B ≤ (2 : ℝ) ^ b)
    (hq : b + 2 * l + j + 3 ≤ q) (hpad : L + L ≤ 2 ^ l + 1)
    (V : ℕ → List GaussianInt) (hlenV : ∀ n < M, (V n).length = L)
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (n : Fin M) (lo : ZMod s) (c : ZMod s → ℝ) (r y : ℕ → ℝ)
    (tail tape : List (Fin (A + 4)))
    (htape : tape = cstream A w ((branchDifference q l M L
      (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
      (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)) V).map
      (fun x => tdivN q (x * reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)))) ++ tail)
    (hr : ∀ k < L, |r k - 1 / PhaseCellMatrix.weight s t p u lo k| ≤ 1 / (2 : ℝ) ^ j)
    (hv : ∀ k < L, |B * (value q (block (V n) k)).re - c (lo + (k : ZMod s)) * r k| ≤ 1 / (2 : ℝ) ^ j)
    (hy : ∀ k < L, |y k - PhaseCellMatrix.weight s t p u lo k * cellOutputValue q l w L B n tape k| ≤
      1 / (2 : ℝ) ^ j) :
    (preparedRun s t p u q l w M L j B V n r y tape).Valid s t p u lo L c (1 / (2 : ℝ) ^ j) B := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hprecision : 13 ≤ 2 ^ 15 * p := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  have hqj : j + 2 ≤ q := by omega
  have hlower := cell_stage_precision hBb hq
  have hr0 : (1 : ℝ) ≤ (2 ^ l : ℕ) := by exact_mod_cast (show 1 ≤ 2 ^ l from Nat.one_le_two_pow)
  have he : 4 * B * (2 ^ l : ℕ) ≤ 8 * B * (2 ^ l : ℕ) ^ 2 := by
    calc
      _ ≤ 8 * B * (2 ^ l : ℕ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hupper := (div_le_div_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 2 ^ q)).trans hlower
  apply interiorRun_valid hA hw B (1 / (2 : ℝ) ^ j) hB hpad
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)) V
    (by intro k hk; simp) (by intro k hk; simp) hlenV
    (fun _ _ => columnWords_disk hprecision hs hst hu (by omega) (by omega))
    (fun _ _ => reversedColumnWords_disk hprecision hs hst hu (by omega) (by omega)) hV
    (fun _ _ => normalizedWords_real q _) (fun _ _ => normalizedWords_real q _)
    (reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (reciprocalWord_norm hprecision hs hst hu hL (by omega)) rfl hupper hlower
    n lo c r y tail tape htape
    (columnWords_error_precision hprecision hs hst hu hqj)
    (reversedColumnWords_error_precision hprecision hs hst hu hqj)
    (reciprocalWord_error_precision hprecision hs hst hu hqj hL) hr hv hy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
