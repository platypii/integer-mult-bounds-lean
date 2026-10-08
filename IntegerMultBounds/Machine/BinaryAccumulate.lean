import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.BinaryAdd

/-! Literal in-place least-significant-first binary accumulation. Two tapes
and three states: the addend is scanned forward together with the
accumulator, a missing high bit on either tape read as zero, each column's
sum written back over the accumulator cell, the carry living in finite
control. A final carry extends the accumulator by one cell. The addend is
preserved; the cost is the larger width plus one. -/

namespace IntegerMultBounds.Machine.BinaryAccumulate

variable {a : ℕ}

open BinaryPad (columns inputSymbol outputBit padded)
open BinaryAdd (sumBit carryBit digits overflow carryWord result carryState finalState)
open BinaryCompare (isInput putWord_blank_tail)

/-- Zero for no carry, one for a carry, two after writing a final carry. -/
def program (a : ℕ) : Program 2 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 2 then none
    else if symbols 0 = blank ∧ symbols 1 = blank then
      if state = 1 then some (2, fun i =>
        if i = 1 then (bitSymbol true, .right) else (symbols i, .stay)) else none
    else if isInput (symbols 0) ∧ isInput (symbols 1) then
      let c := decide (state = 1)
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (carryState (carryBit c x y), fun i =>
        (if i = 1 then bitSymbol (sumBit c x y) else symbols i, .right))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (state : Fin 3) : Config 2 3 a where
  state := state
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

private theorem column_step (c : Bool) (x y : Option Bool) (hv : x ≠ none ∨ y ≠ none)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = inputSymbol y) :
    step (program a) (cfg f g p q (carryState c)) =
      some (cfg f (Function.update g q (bitSymbol (sumBit c (outputBit x) (outputBit y))))
        (p + 1) (q + 1) (carryState (carryBit c (outputBit x) (outputBit y)))) := by
  have ht : (program a).transition (carryState c)
      (fun i => (cfg f g p q (carryState c)).tape i ((cfg f g p q (carryState c)).head i)) =
      some (carryState (carryBit c (outputBit x) (outputBit y)), fun i =>
        (if i = 1 then bitSymbol (sumBit c (outputBit x) (outputBit y))
          else (cfg f g p q (carryState c)).tape i ((cfg f g p q (carryState c)).head i),
          Move.right)) := by
    cases c <;> rcases x with _ | x <;> rcases y with _ | y <;> simp at hv <;>
      (try cases x) <;> (try cases y) <;>
      simp [program, cfg, carryState, carryBit, sumBit, isInput, hx, hy, inputSymbol, outputBit,
        blank, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

/-- The pairs of bits read from aligned columns. -/
def pairs (cols : List (Option Bool × Option Bool)) : List (Bool × Bool) :=
  cols.map fun c => (outputBit c.1, outputBit c.2)

/-- One transition per aligned column; the addend tape is retained entirely
and the accumulator receives the column sums. -/
theorem columns_run (c : Bool) (cols : List (Option Bool × Option Bool))
    (hv : ∀ col ∈ cols, col.1 ≠ none ∨ col.2 ≠ none) (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    run (program a) cols.length
      (cfg (putWord f p (cols.map (fun col => inputSymbol col.1)))
        (putWord g q (cols.map (fun col => inputSymbol col.2))) p q (carryState c)) =
      some (cfg (putWord f p (cols.map (fun col => inputSymbol col.1)))
        (putWord g q ((digits c (pairs cols)).map bitSymbol))
        (p + cols.length) (q + cols.length) (carryState (overflow c (pairs cols)))) := by
  induction cols generalizing c f g p q with
  | nil => simp [run, putWord, pairs, digits, overflow]
  | cons col cols ih =>
    rcases col with ⟨x, y⟩
    have hs := column_step c x y (hv (x, y) (by simp))
      (putWord f p (((x, y) :: cols).map (fun col => inputSymbol col.1)))
      (putWord g q (((x, y) :: cols).map (fun col => inputSymbol col.2))) p q
      (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
    simp only [List.length_cons, run, hs, Option.bind_some]
    simp only [List.map_cons, putWord_replace_head]
    have hr := ih (carryBit c (outputBit x) (outputBit y)) (fun col hc => hv col (by simp [hc]))
      (Function.update f p (inputSymbol x))
      (Function.update g q (bitSymbol (sumBit c (outputBit x) (outputBit y)))) (p + 1) (q + 1)
    simpa only [← putWord_cons, pairs, List.map_cons, digits, overflow, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm, add_left_comm] using hr

private theorem final_carry_step (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    step (program a) (cfg f g p q 1) =
      some (cfg f (Function.update g q (bitSymbol true)) p (q + 1) 2) := by
  have ht : (program a).transition 1 (fun i => (cfg f g p q 1).tape i ((cfg f g p q 1).head i)) =
      some (2, fun i => if i = 1 then (bitSymbol true, Move.right)
        else ((cfg f g p q 1).tape i ((cfg f g p q 1).head i), Move.stay)) := by
    simp [program, cfg, hf, hg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

private theorem finish_exact (c : Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    run (program a) (carryWord c).length (cfg f g p q (carryState c)) =
      some (cfg f (putWord g q ((carryWord c).map bitSymbol)) p (q + (carryWord c).length)
        (finalState c)) ∧
    step (program a) (cfg f (putWord g q ((carryWord c).map bitSymbol)) p
      (q + (carryWord c).length) (finalState c)) = none := by
  cases c with
  | false => simp [carryWord, carryState, finalState, run, step, program, cfg, putWord, hf, hg]
  | true =>
    constructor
    · simpa only [carryWord, carryState, finalState, ↓reduceIte, List.length_singleton,
        List.map_cons, List.map_nil, putWord, run_one, Nat.cast_one] using final_carry_step f g p q hf hg
    · simp [carryWord, finalState, step, program, cfg]

/-- The common width of addend and accumulator. -/
def width (xs acc : List Bool) : ℕ := max xs.length acc.length

theorem padded_left_length (xs acc : List Bool) :
    (padded xs (width xs acc)).length = width xs acc :=
  BinaryPad.padded_length _ _ (Nat.le_max_left _ _)

theorem padded_right_length (xs acc : List Bool) :
    (padded acc (width xs acc)).length = width xs acc :=
  BinaryPad.padded_length _ _ (Nat.le_max_right _ _)

/-- The accumulator after the addition. -/
def sumWord (xs acc : List Bool) : List Bool :=
  result false ((padded xs (width xs acc)).zip (padded acc (width xs acc)))

theorem sumWord_value (xs acc : List Bool) :
    Counter.value (sumWord xs acc) = Counter.value xs + Counter.value acc := by
  have h := BinaryAdd.result_value false (padded xs (width xs acc)) (padded acc (width xs acc)) (by
    rw [padded_left_length, padded_right_length])
  simpa only [sumWord, BinaryAdd.bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    BinaryPad.padded_value] using h

theorem sumWord_length_le (xs acc : List Bool) : (sumWord xs acc).length ≤ width xs acc + 1 := by
  have h := BinaryAdd.result_length_le false (padded xs (width xs acc)) (padded acc (width xs acc)) (by
    rw [padded_left_length, padded_right_length])
  rwa [padded_left_length] at h

theorem sumWord_length_ge (xs acc : List Bool) : width xs acc ≤ (sumWord xs acc).length := by
  have h := BinaryAdd.result_length false (padded xs (width xs acc)) (padded acc (width xs acc)) (by
    rw [padded_left_length, padded_right_length])
  rw [padded_left_length] at h
  unfold sumWord
  omega

/-- Exact execution: scan to the common width, write a final carry if any,
halt. The addend's whole tape is preserved. -/
theorem accumulate_exact (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs acc → f (p + j) = blank)
    (hg : ∀ j : ℕ, acc.length ≤ j → j ≤ width xs acc → g (q + j) = blank) :
    run (program a) (sumWord xs acc).length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q ((sumWord xs acc).map bitSymbol))
        (p + width xs acc) (q + (sumWord xs acc).length)
        (finalState (overflow false ((padded xs (width xs acc)).zip (padded acc (width xs acc)))))) ∧
    step (program a) (cfg (putWord f p (xs.map bitSymbol))
      (putWord g q ((sumWord xs acc).map bitSymbol)) (p + width xs acc)
      (q + (sumWord xs acc).length)
      (finalState (overflow false ((padded xs (width xs acc)).zip (padded acc (width xs acc)))))) =
      none := by
  have hmax : width xs acc = max xs.length acc.length := rfl
  have hfx : putWord f p (xs.map bitSymbol) =
      putWord f p ((columns xs acc).map (fun col => inputSymbol col.1)) := by
    rw [BinaryPad.columns_left_input, putWord_append, putWord_blank_tail]
    intro j hj
    rw [show p + (xs.map (bitSymbol (a := a))).length + (j : ℤ) = p + ((xs.length + j : ℕ) : ℤ) by
      push_cast; simp; ring]
    exact hf _ (by omega) (by rw [hmax]; omega)
  have hgy : putWord g q (acc.map bitSymbol) =
      putWord g q ((columns xs acc).map (fun col => inputSymbol col.2)) := by
    rw [BinaryPad.columns_right_input, putWord_append, putWord_blank_tail]
    intro j hj
    rw [show q + (acc.map (bitSymbol (a := a))).length + (j : ℤ) = q + ((acc.length + j : ℕ) : ℤ) by
      push_cast; simp; ring]
    exact hg _ (by omega) (by rw [hmax]; omega)
  have hw : (columns xs acc).length = width xs acc := BinaryPad.columns_length xs acc
  have hpairs : pairs (columns xs acc) = (padded xs (width xs acc)).zip (padded acc (width xs acc)) := by
    rw [pairs, hmax, ← BinaryPad.columns_left_output, ← BinaryPad.columns_right_output, List.zip_map']
  have hr := columns_run false (columns xs acc) (BinaryPad.columns_valid xs acc) f g p q
  rw [hpairs, hw, show carryState false = (0 : Fin 3) from rfl] at hr
  set D := (digits false ((padded xs (width xs acc)).zip (padded acc (width xs acc)))).map
    (bitSymbol (a := a)) with hD
  set C := (carryWord (overflow false ((padded xs (width xs acc)).zip
    (padded acc (width xs acc))))).map (bitSymbol (a := a)) with hC
  have hd : D.length = width xs acc := by
    rw [hD, List.length_map, BinaryAdd.digits_length, List.length_zip, padded_left_length,
      padded_right_length, min_self]
  have hblankf : putWord f p ((columns xs acc).map (fun col => inputSymbol col.1))
      (p + width xs acc) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [hw])), hf _ (by rw [hmax]; exact Nat.le_max_left _ _) le_rfl]
  have hblankg : putWord g q D (q + width xs acc) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [hd])), hg _ (by rw [hmax]; exact Nat.le_max_right _ _) le_rfl]
  have he := finish_exact (overflow false ((padded xs (width xs acc)).zip (padded acc (width xs acc))))
    (putWord f p ((columns xs acc).map (fun col => inputSymbol col.1))) (putWord g q D)
    (p + width xs acc) (q + width xs acc) hblankf hblankg
  have hword : putWord (putWord g q D) (q + width xs acc) C = putWord g q ((sumWord xs acc).map bitSymbol) := by
    have h := putWord_append_forward g q D C
    rw [hd] at h
    rw [h, hD, hC, ← List.map_append]
    rfl
  have hlen : (sumWord xs acc).length = width xs acc +
      (carryWord (overflow false ((padded xs (width xs acc)).zip (padded acc (width xs acc))))).length := by
    have h := BinaryAdd.result_length false (padded xs (width xs acc)) (padded acc (width xs acc)) (by
      rw [padded_left_length, padded_right_length])
    rw [padded_left_length] at h
    rw [sumWord, h]
  have hq : q + (width xs acc : ℤ) + ((carryWord (overflow false ((padded xs (width xs acc)).zip
      (padded acc (width xs acc))))).length : ℤ) = q + ((sumWord xs acc).length : ℤ) := by
    rw [hlen]; push_cast; ring
  rw [hword, hq] at he
  refine ⟨?_, by rw [hfx]; exact he.2⟩
  rw [hfx, hgy]
  conv_lhs => rw [hlen, run_add]
  rw [hr]
  simp only [Option.bind_some]
  exact he.1

/-- The accumulation contract: the addend is preserved, the accumulator holds
the exact sum, the heads advance to the common width and the sum's end. -/
theorem accumulate_hoare (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs acc → f (p + j) = blank)
    (hg : ∀ j : ℕ, acc.length ≤ j → j ≤ width xs acc → g (q + j) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0).tapes)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol))
        (putWord g q ((sumWord xs acc).map bitSymbol)) (p + width xs acc)
        (q + (sumWord xs acc).length) 0).tapes)
      (width xs acc + 1) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := accumulate_exact xs acc f g p q hf hg
  exact ⟨_, _, sumWord_length_le xs acc, hr, hh, rfl⟩

end IntegerMultBounds.Machine.BinaryAccumulate
