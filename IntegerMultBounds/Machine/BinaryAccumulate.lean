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
open BinaryCompare (isInput)

/-- Zero for no carry, one for a carry, two after writing a final carry. The
addend head advances only over addend bits and parks on the addend's blank. -/
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
        if i = 1 then (bitSymbol (sumBit c x y), .right)
        else (symbols i, if symbols i = blank then .stay else .right))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (state : Fin 3) : Config 2 3 a where
  state := state
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

/-- The addend head moves only over an actual bit. -/
def shift (x : Option Bool) : ℤ := if x = none then 0 else 1

private theorem column_step (c : Bool) (x y : Option Bool) (hv : x ≠ none ∨ y ≠ none)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = inputSymbol y) :
    step (program a) (cfg f g p q (carryState c)) =
      some (cfg f (Function.update g q (bitSymbol (sumBit c (outputBit x) (outputBit y))))
        (p + shift x) (q + 1) (carryState (carryBit c (outputBit x) (outputBit y)))) := by
  have ht : (program a).transition (carryState c)
      (fun i => (cfg f g p q (carryState c)).tape i ((cfg f g p q (carryState c)).head i)) =
      some (carryState (carryBit c (outputBit x) (outputBit y)), fun i =>
        if i = 1 then (bitSymbol (sumBit c (outputBit x) (outputBit y)), Move.right)
        else ((cfg f g p q (carryState c)).tape i ((cfg f g p q (carryState c)).head i),
          if x = none then Move.stay else Move.right)) := by
    cases c <;> rcases x with _ | x <;> rcases y with _ | y <;> simp at hv <;>
      (try cases x) <;> (try cases y) <;>
      simp [program, cfg, carryState, carryBit, sumBit, isInput, hx, hy, inputSymbol, outputBit,
        blank, bitSymbol]
    all_goals (funext i; fin_cases i <;> simp [hx, inputSymbol, blank, bitSymbol])
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rcases x with _ | x <;> simp [shift]
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

/-- The common width of addend and accumulator. -/
def width (xs acc : List Bool) : ℕ := max xs.length acc.length

theorem padded_left_length (xs acc : List Bool) :
    (padded xs (width xs acc)).length = width xs acc :=
  BinaryPad.padded_length _ _ (Nat.le_max_left _ _)

theorem padded_right_length (xs acc : List Bool) :
    (padded acc (width xs acc)).length = width xs acc :=
  BinaryPad.padded_length _ _ (Nat.le_max_right _ _)

/-- The aligned columns of addend and accumulator, read as bits. -/
def pairs (xs acc : List Bool) : List (Bool × Bool) :=
  (padded xs (width xs acc)).zip (padded acc (width xs acc))

theorem pairs_cons_cons (x y : Bool) (xs acc : List Bool) :
    pairs (x :: xs) (y :: acc) = (x, y) :: pairs xs acc := by
  simp [pairs, padded, width, List.length_cons, max_add_add_right, Nat.add_sub_add_right]

theorem pairs_nil_cons (y : Bool) (acc : List Bool) :
    pairs [] (y :: acc) = (false, y) :: pairs [] acc := by
  simp [pairs, padded, width, List.replicate_succ]

theorem pairs_cons_nil (x : Bool) (xs : List Bool) :
    pairs (x :: xs) [] = (x, false) :: pairs xs [] := by
  simp [pairs, padded, width, List.replicate_succ]

theorem width_cons_cons (x y : Bool) (xs acc : List Bool) :
    width (x :: xs) (y :: acc) = width xs acc + 1 := by
  simp [width, max_add_add_right]

theorem width_nil_cons (y : Bool) (acc : List Bool) : width [] (y :: acc) = width [] acc + 1 := by
  simp [width]

theorem width_cons_nil (x : Bool) (xs : List Bool) : width (x :: xs) [] = width xs [] + 1 := by
  simp [width]

/-- One transition per aligned column; the addend tape is retained entirely,
its head parks on the addend's blank end, and the accumulator receives the
column sums. -/
theorem columns_run (c : Bool) (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + xs.length) = blank)
    (hg : ∀ j : ℕ, acc.length ≤ j → j < width xs acc → g (q + j) = blank) :
    run (program a) (width xs acc)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q (carryState c)) =
      some (cfg (putWord f p (xs.map bitSymbol))
        (putWord g q ((digits c (pairs xs acc)).map bitSymbol))
        (p + xs.length) (q + width xs acc) (carryState (overflow c (pairs xs acc)))) := by
  induction xs generalizing acc c f g p q with
  | nil =>
    induction acc generalizing c g q with
    | nil => simp [run, putWord, pairs, padded, width, digits, overflow]
    | cons y acc ih =>
      have hs := column_step c none (some y) (by simp) (putWord f p ([].map bitSymbol))
        (putWord g q ((y :: acc).map bitSymbol)) p q (by simpa [putWord, inputSymbol] using hf)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_nil_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, List.map_nil, shift,
        ↓reduceIte, add_zero, outputBit, Option.getD_none, Option.getD_some]
      have hr := ih (carryBit c false y) (Function.update g q (bitSymbol (sumBit c false y)))
        (q + 1) (fun j hj hjw => by
          rw [Function.update_of_ne (by omega), show q + 1 + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hg (j + 1) (by simpa using hj) (by rw [width_nil_cons]; omega))
      simp only [List.map_nil, putWord] at hr ⊢
      rw [hr]
      simp only [pairs_nil_cons, digits, overflow, List.map_cons, putWord_cons, List.length_nil,
        Nat.cast_zero, add_zero]
      congr 2
      push_cast; ring
  | cons x xs ih =>
    cases acc with
    | nil =>
      have hs := column_step c (some x) none (by simp) (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ([].map bitSymbol)) p q (by rw [List.map_cons, putWord_head]; rfl)
        (by simpa [putWord, inputSymbol] using hg 0 (by simp) (by rw [width_cons_nil]; omega))
      rw [width_cons_nil, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_cons, List.map_nil, shift, putWord,
        ↓reduceIte, reduceCtorEq, outputBit, Option.getD_none, Option.getD_some]
      have hr := ih (carryBit c x false) [] (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol (sumBit c x false))) (p + 1) (q + 1)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (xs.length : ℤ) = p + ((x :: xs).length : ℕ) by
            simp; ring]; exact hf)
        (fun j hj hjw => by
          rw [Function.update_of_ne (by omega), show q + 1 + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hg (j + 1) (by simp) (by rw [width_cons_nil]; omega))
      simp only [List.map_nil, putWord] at hr
      rw [hr]
      simp only [pairs_cons_nil, digits, overflow, List.map_cons, putWord_cons, List.length_cons]
      congr 2
      · push_cast; ring
      · push_cast; ring
    | cons y acc =>
      have hs := column_step c (some x) (some y) (by simp) (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ((y :: acc).map bitSymbol)) p q (by rw [List.map_cons, putWord_head]; rfl)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_cons_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, shift, ↓reduceIte,
        reduceCtorEq, outputBit, Option.getD_some]
      rw [putWord_cons f]
      have hr := ih (carryBit c x y) acc (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol (sumBit c x y))) (p + 1) (q + 1)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (xs.length : ℤ) = p + ((x :: xs).length : ℕ) by
            simp; ring]; exact hf)
        (fun j hj hjw => by
          rw [Function.update_of_ne (by omega), show q + 1 + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hg (j + 1) (by simpa using hj) (by rw [width_cons_cons]; omega))
      rw [hr]
      simp only [pairs_cons_cons, digits, overflow, List.map_cons, putWord_cons, List.length_cons]
      congr 2
      · push_cast; ring
      · push_cast; ring

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

/-- The accumulator after the addition. -/
def sumWord (xs acc : List Bool) : List Bool := result false (pairs xs acc)

theorem pairs_lengths (xs acc : List Bool) :
    (padded xs (width xs acc)).length = (padded acc (width xs acc)).length := by
  rw [padded_left_length, padded_right_length]

theorem sumWord_value (xs acc : List Bool) :
    Counter.value (sumWord xs acc) = Counter.value xs + Counter.value acc := by
  have h := BinaryAdd.result_value false (padded xs (width xs acc)) (padded acc (width xs acc))
    (pairs_lengths xs acc)
  simpa only [sumWord, pairs, BinaryAdd.bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    BinaryPad.padded_value] using h

theorem sumWord_length (xs acc : List Bool) :
    (sumWord xs acc).length = width xs acc + (carryWord (overflow false (pairs xs acc))).length := by
  have h := BinaryAdd.result_length false (padded xs (width xs acc)) (padded acc (width xs acc))
    (pairs_lengths xs acc)
  rw [padded_left_length] at h
  exact h

theorem sumWord_length_le (xs acc : List Bool) : (sumWord xs acc).length ≤ width xs acc + 1 := by
  rw [sumWord_length]
  cases overflow false (pairs xs acc) <;> simp [carryWord]

theorem sumWord_length_ge (xs acc : List Bool) : width xs acc ≤ (sumWord xs acc).length := by
  rw [sumWord_length]; omega

/-- Exact execution: scan to the common width, write a final carry if any,
halt. The addend's whole tape is preserved and its head parks on its end. -/
theorem accumulate_exact (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + xs.length) = blank)
    (hg : ∀ j : ℕ, acc.length ≤ j → j ≤ width xs acc → g (q + j) = blank) :
    run (program a) (sumWord xs acc).length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q ((sumWord xs acc).map bitSymbol))
        (p + xs.length) (q + (sumWord xs acc).length)
        (finalState (overflow false (pairs xs acc)))) ∧
    step (program a) (cfg (putWord f p (xs.map bitSymbol))
      (putWord g q ((sumWord xs acc).map bitSymbol)) (p + xs.length)
      (q + (sumWord xs acc).length) (finalState (overflow false (pairs xs acc)))) = none := by
  have hr := columns_run false xs acc f g p q hf (fun j hj hjw => hg j hj hjw.le)
  rw [show carryState false = (0 : Fin 3) from rfl] at hr
  set D := (digits false (pairs xs acc)).map (bitSymbol (a := a)) with hD
  set C := (carryWord (overflow false (pairs xs acc))).map (bitSymbol (a := a)) with hC
  have hd : D.length = width xs acc := by
    rw [hD, List.length_map, BinaryAdd.digits_length, pairs, List.length_zip, padded_left_length,
      padded_right_length, min_self]
  have hblankf : putWord f p (xs.map bitSymbol) (p + xs.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
  have hblankg : putWord g q D (q + width xs acc) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [hd])), hg (width xs acc) (Nat.le_max_right _ _) le_rfl]
  have he := finish_exact (overflow false (pairs xs acc)) (putWord f p (xs.map bitSymbol))
    (putWord g q D) (p + xs.length) (q + width xs acc) hblankf hblankg
  have hword : putWord (putWord g q D) (q + width xs acc) C =
      putWord g q ((sumWord xs acc).map bitSymbol) := by
    have h := putWord_append_forward g q D C
    rw [hd] at h
    rw [h, hD, hC, ← List.map_append]
    rfl
  have hq : q + (width xs acc : ℤ) + ((carryWord (overflow false (pairs xs acc))).length : ℤ) =
      q + ((sumWord xs acc).length : ℤ) := by
    rw [sumWord_length]; push_cast; ring
  rw [hword, hq] at he
  refine ⟨?_, he.2⟩
  conv_lhs => rw [sumWord_length, run_add]
  rw [hr]
  simp only [Option.bind_some]
  exact he.1

/-- The accumulation contract: the addend is preserved with its head parked
on its blank end, the accumulator holds the exact sum with its head at the
sum's end. -/
theorem accumulate_hoare (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + xs.length) = blank)
    (hg : ∀ j : ℕ, acc.length ≤ j → j ≤ width xs acc → g (q + j) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0).tapes)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol))
        (putWord g q ((sumWord xs acc).map bitSymbol)) (p + xs.length)
        (q + (sumWord xs acc).length) 0).tapes)
      (width xs acc + 1) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := accumulate_exact xs acc f g p q hf hg
  exact ⟨_, _, sumWord_length_le xs acc, hr, hh, rfl⟩

end IntegerMultBounds.Machine.BinaryAccumulate
