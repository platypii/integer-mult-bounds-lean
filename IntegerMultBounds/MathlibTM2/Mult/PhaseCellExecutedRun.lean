module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorRun

/-! # Cell validity for the actual executed arithmetic data

Input normalization, the interior kernel and final similarity multiplication
use their actual truncated numerators and signed output words. No equality with
the rational-floor numerical reference or assumed stage-error facts is needed.
The bank-to-bank arithmetic composition is proved in `PhaseCellConstructedExecution`;
setup generation, publication and boundary/line composition remain open.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- The real cell run read from the actual arithmetic stage outputs. -/
noncomputable def executedRun {A : ℕ} (s t p u q l w M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n : ℕ) (tail : List (Fin (A + 4))) : PhaseCellMatrix.CellRun :=
  preparedRun s t p u q l w M L j ((2 : ℝ) ^ inputExponent p cExp)
    (executedInputRows s t p u q L cExp lo C) n
    (fun k => (value q (reciprocalWeightWord q (weightData s t p u (lo n) k))).re)
    (fun k => (value q (decodeWord (((cstream A w (executedOutputWords s t p u q l M L j cExp lo C) ++ tail).drop
      ((n * L + (L - 1 - k)) * w)).take w))).re)
    (cstream A w (executedInteriorWords s t p u q l M L j cExp lo C) ++ tail)

/-- Complete cell validity for the data emitted by the individually verified
machine stages. Ambient weights are looked up in the true reversed row order. -/
theorem executedRun_valid {A q l w M L s t p u j cExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hw : q + inputExponent p cExp + 2 * l + 6 ≤ w)
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hq : inputExponent p cExp + 2 * l + j + 5 ≤ q)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value q (C n k)‖ ≤ (2 : ℝ) ^ cExp)
    (n : Fin M) (tail : List (Fin (A + 4))) :
    (executedRun s t p u q l w M L j cExp lo C n tail).Valid s t p u (lo n) L
      (fun k => (value q (C n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hgrid := (weight_stage_precision (b := 0) (j := j) (q := q) (by omega)).2
  unfold executedRun
  apply preparedRun_valid (b := inputExponent p cExp) hA (by omega) hp hst hu hL
    ((2 : ℝ) ^ inputExponent p cExp) (by positivity) le_rfl (by omega) hpad
    (executedInputRows s t p u q L cExp lo C) (by intro m hm; simp)
    (executedInputRows_disk hp hs hαu hθ hgap hbudget lo C hC)
    n (lo n) (fun k => (value q (C n k)).re)
    (fun k => (value q (reciprocalWeightWord q (weightData s t p u (lo n) k))).re)
    (fun k => (value q (decodeWord (((cstream A w (executedOutputWords s t p u q l M L j cExp lo C) ++ tail).drop
      ((n.val * L + (L - 1 - k)) * w)).take w))).re)
    tail (cstream A w (executedInteriorWords s t p u q l M L j cExp lo C) ++ tail) rfl ?_ ?_ ?_
  · intro k hk
    have h := reciprocalWeightWord_error q (weightData s t p u (lo n) k)
    simpa only [weightData_cast] using h.trans hgrid
  · intro k hk
    exact executedInputRows_error (by omega) lo C n k hk
  · intro k hk
    let idx := cellIndex n (⟨k, hk⟩ : Fin L)
    let inner := executedInteriorWords s t p u q l M L j cExp lo C
    let table := executedOutputTable s t p u M L lo
    have hi : idx.val < inner.length := by simpa only [inner, executedInteriorWords_length] using idx.isLt
    have hit : idx.val < table.length := by
      simpa only [table, executedOutputTable, reversedRowTable_length] using idx.isLt
    have hlen : inner.length = table.length := by simp [inner, table, executedOutputTable]
    have hnorm : ∀ z ∈ inner, ‖value q z‖ ≤ 4 :=
      executedInteriorWords_norm hp hs hst hu hL (by omega) hαu hθ hgap hbudget hpad lo C hC
    have htable : ∀ a ∈ table, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1 := by
      intro a ha
      change a ∈ List.ofFn (fun i : Fin (M * L) =>
        weightData s t p u (lo (i.val / L)) (L - 1 - i.val % L)) at ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      have h := weightData_bounds hp hs hαu hθ hgap hbudget (lo (i.val / L)) (L - 1 - i.val % L)
      exact ⟨(lt_of_lt_of_le (by positivity) h.1).le, h.2⟩
    have hget : table.getD idx.val 0 = weightData s t p u (lo n) k :=
      reversedRowTable_getD (fun m i => weightData s t p u (lo m) i) 0 n ⟨k, hk⟩
    have hentry : table[idx.val] = weightData s t p u (lo n) k := by
      simpa only [List.getD_eq_getElem _ _ hit] using hget
    have hread : decodeWord (((cstream A w inner ++ tail).drop (idx.val * w)).take w) = inner[idx.val] := by
      rw [cstream_word w _ tail idx.val hi]
      apply decodeWord_of_fits hA (by omega)
      apply fits_of_value_power (q := q) (e := 2) (by omega)
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact hnorm _ (List.getElem_mem hi)
    have hy := weightedOutputNumerators_word_error (A := A) (q := q) (d := inputExponent p cExp + 2 * l + 2)
      (w := w) hA (by omega) inner table hlen hnorm htable tail idx.val hi
    have hy' := hy.trans (output_weight_precision (j := j) (by omega))
    rw [hentry, weightData_cast, cell_output_scale] at hy'
    have hread' : decodeWord (((cstream A w inner ++ tail).drop
        ((n.val * L + (L - 1 - k)) * w)).take w) = inner[idx.val] := hread
    change |(value q (decodeWord (((cstream A w (weightedOutputNumerators q
        (inputExponent p cExp + 2 * l + 2) inner table) ++ tail).drop (idx.val * w)).take w))).re -
      PhaseCellMatrix.weight s t p u (lo n) k *
        (4 * (2 : ℝ) ^ inputExponent p cExp * (2 ^ l : ℕ) ^ 2 *
          (value q (decodeWord (((cstream A w inner ++ tail).drop
            ((n.val * L + (L - 1 - k)) * w)).take w))).re)| ≤ 1 / (2 : ℝ) ^ j
    rw [hread']
    exact hy'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
