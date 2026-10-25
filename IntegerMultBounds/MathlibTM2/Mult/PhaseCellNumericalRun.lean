module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorRun

/-! # A complete numerical cell run from rational data

All fields are obtained from computable rational data and the actual interior
output tape. Validity has no assumed stage-error oracle. This does not execute
the setup or the three weight stages on tape; those machine and cost proofs
remain obligations of the composed solver.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast

/-- One normalized input row per cell origin and rational right-hand side. -/
def weightedInputRows (s t p u q L cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → ℚ) (n : ℕ) : List GaussianInt :=
  (List.range L).map (fun k : ℕ => weightedInputWord q (inputExponent p cExp)
    (C n (lo n + (k : ZMod s))) (weightData s t p u (lo n) k))

@[simp] theorem weightedInputRows_length (s t p u q L cExp : ℕ)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → ℚ) (n : ℕ) :
    (weightedInputRows s t p u q L cExp lo C n).length = L := by simp [weightedInputRows]

/-- Rational interpretation of the computed scalar output and its exact scale. -/
def rationalOutputValue {A : ℕ} (q l w L b n : ℕ) (tape : List (Fin (A + 4))) (i : ℕ) : ℚ :=
  4 * (2 : ℚ) ^ b * (2 ^ l : ℕ) ^ 2 *
    rationalValue q (decodeWord ((tape.drop ((n * L + (L - 1 - i)) * w)).take w))

@[simp] theorem rationalOutputValue_cast {A : ℕ} (q l w L b n : ℕ)
    (tape : List (Fin (A + 4))) (i : ℕ) :
    (rationalOutputValue q l w L b n tape i : ℝ) =
      cellOutputValue q l w L ((2 : ℝ) ^ b) n tape i := by
  simp [rationalOutputValue, cellOutputValue]

/-- The full numerical run, including reciprocal weights, normalized inputs and
final weight multiplication on the computed interior output. -/
noncomputable def numericalRun {A : ℕ} (s t p u q l w M L j cExp : ℕ)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → ℚ) (n : ℕ) (tape : List (Fin (A + 4))) :
    PhaseCellMatrix.CellRun :=
  preparedRun s t p u q l w M L j ((2 : ℝ) ^ inputExponent p cExp)
    (weightedInputRows s t p u q L cExp lo C) n
    (fun k => (value q (reciprocalWeightWord q (weightData s t p u (lo n) k))).re)
    (fun k => (value q (weightedOutputWord q (weightData s t p u (lo n) k)
      (rationalOutputValue q l w L (inputExponent p cExp) n tape k))).re) tape

/-- Complete numerical validity for the generated arrays and actual interior
output. Every stage-error clause is proved; tape generation and execution of
the weight stages are not asserted by this numerical theorem. -/
theorem numericalRun_valid {A q l w M L s t p u j cExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hw : q + 4 ≤ w) (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hq : inputExponent p cExp + 2 * l + j + 3 ≤ q)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → ℚ)
    (hC : ∀ n < M, ∀ k, |(C n k : ℝ)| ≤ (2 : ℝ) ^ cExp)
    (n : Fin M) (tail tape : List (Fin (A + 4)))
    (htape : tape = cstream A w ((branchDifference q l M L
      (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
      (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
      (weightedInputRows s t p u q L cExp lo C)).map
      (fun x => tdivN q (x * reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2)))) ++ tail) :
    (numericalRun s t p u q l w M L j cExp lo C n tape).Valid s t p u (lo n) L
      (fun k => (C n k : ℝ)) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hprec := weight_stage_precision (b := inputExponent p cExp) (j := j) (q := q) (by omega)
  apply preparedRun_valid hA hw hp hst hu hL ((2 : ℝ) ^ inputExponent p cExp)
    (by positivity) le_rfl hq hpad (weightedInputRows s t p u q L cExp lo C)
    (by intro k hk; simp) ?_ n (lo n) (fun k => (C n k : ℝ))
    (fun k => (value q (reciprocalWeightWord q (weightData s t p u (lo n) k))).re)
    (fun k => (value q (weightedOutputWord q (weightData s t p u (lo n) k)
      (rationalOutputValue q l w L (inputExponent p cExp) n tape k))).re)
    tail tape htape ?_ ?_ ?_
  · intro m hm z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact weightedInputWord_disk (q := q) (cExp := cExp) (e := 8 * p + 1) (by omega) _ _
      (hC m hm _) (weightData_bounds hp hs hαu hθ hgap hbudget (lo m) k).1
  · intro k hk
    have h := reciprocalWeightWord_error q (weightData s t p u (lo n) k)
    simpa only [weightData_cast] using h.trans hprec.2
  · intro k hk
    have hget : block (weightedInputRows s t p u q L cExp lo C n) k =
        weightedInputWord q (inputExponent p cExp) (C n (lo n + (k : ZMod s)))
          (weightData s t p u (lo n) k) := by
      simp [block, weightedInputRows, hk]
    change |(2 : ℝ) ^ inputExponent p cExp *
      (value q (block (weightedInputRows s t p u q L cExp lo C n) k)).re -
      (C n (lo n + (k : ZMod s)) : ℝ) *
        (value q (reciprocalWeightWord q (weightData s t p u (lo n) k))).re| ≤ _
    rw [hget]
    exact (weightedInputWord_error q (inputExponent p cExp) _ _).trans hprec.1
  · intro k hk
    have h := weightedOutputWord_error q (weightData s t p u (lo n) k)
      (rationalOutputValue q l w L (inputExponent p cExp) n tape k)
    simpa only [weightData_cast, rationalOutputValue_cast] using h.trans hprec.2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
