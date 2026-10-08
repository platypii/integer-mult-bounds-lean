import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.BinarySub

/-! Literal in-place least-significant-first binary subtraction. Two tapes
and two states: the subtrahend is scanned forward together with the
minuend, a missing high bit on either tape read as zero, each column's
difference written back over the minuend cell, the borrow living in finite
control; the machine halts on the common blank, so the result is the
difference modulo two to the common width. The subtrahend is preserved with
its head parked on its blank end; the cost is the common width. -/

namespace IntegerMultBounds.Machine.BinaryDecrease

variable {a : ℕ}

open BinaryPad (inputSymbol outputBit padded)
open BinarySub (diffBit borrowBit digits overflow borrowState)
open BinaryCompare (isInput width pairs padded_left_length padded_right_length pairs_cons_cons
  pairs_nil_cons pairs_cons_nil width_cons_cons width_nil_cons width_cons_nil)

/-- Tape zero holds the subtrahend, tape one the minuend. Zero for no borrow,
one for a borrow. Heads advance only over actual bits. -/
def program (a : ℕ) : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if symbols 0 = blank ∧ symbols 1 = blank then none
    else if isInput (symbols 0) ∧ isInput (symbols 1) then
      let c := decide (state = 1)
      let y := decide (symbols 0 = bitSymbol true)
      let x := decide (symbols 1 = bitSymbol true)
      some (borrowState (borrowBit c x y), fun i =>
        if i = 1 then (bitSymbol (diffBit c x y), .right)
        else (symbols i, if symbols i = blank then .stay else .right))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (state : Fin 2) : Config 2 2 a where
  state := state
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

/-- The subtrahend head moves only over an actual bit. -/
def shift (y : Option Bool) : ℤ := if y = none then 0 else 1

private theorem column_step (c : Bool) (y x : Option Bool) (hv : y ≠ none ∨ x ≠ none)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hy : f p = inputSymbol y) (hx : g q = inputSymbol x) :
    step (program a) (cfg f g p q (borrowState c)) =
      some (cfg f (Function.update g q (bitSymbol (diffBit c (outputBit x) (outputBit y))))
        (p + shift y) (q + 1) (borrowState (borrowBit c (outputBit x) (outputBit y)))) := by
  have ht : (program a).transition (borrowState c)
      (fun i => (cfg f g p q (borrowState c)).tape i ((cfg f g p q (borrowState c)).head i)) =
      some (borrowState (borrowBit c (outputBit x) (outputBit y)), fun i =>
        if i = 1 then (bitSymbol (diffBit c (outputBit x) (outputBit y)), Move.right)
        else ((cfg f g p q (borrowState c)).tape i ((cfg f g p q (borrowState c)).head i),
          if y = none then Move.stay else Move.right)) := by
    cases c <;> rcases y with _ | y <;> rcases x with _ | x <;> simp at hv <;>
      (try cases y) <;> (try cases x) <;>
      simp [program, cfg, borrowState, borrowBit, diffBit, isInput, hx, hy, inputSymbol, outputBit,
        blank, bitSymbol]
    all_goals (funext i; fin_cases i <;> simp [hy, inputSymbol, blank, bitSymbol])
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rcases y with _ | y <;> simp [shift]
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

/-- The minuend after the subtraction: the modular difference at the common
width, as a column list with the minuend first. -/
def diffWord (ys xs : List Bool) : List Bool := digits false (pairs xs ys)

private theorem putWord_nil (f : ℤ → Fin (a + 4)) (p : ℤ) : putWord f p [] = f := rfl

/-- One transition per aligned column; the subtrahend tape is retained with
its head parked on its end, and the minuend receives the differences. -/
theorem columns_run (c : Bool) (ys xs : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + ys.length) = blank)
    (hg : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs ys → g (q + j) = blank) :
    run (program a) (width xs ys)
      (cfg (putWord f p (ys.map bitSymbol)) (putWord g q (xs.map bitSymbol)) p q (borrowState c)) =
      some (cfg (putWord f p (ys.map bitSymbol))
        (putWord g q ((digits c (pairs xs ys)).map bitSymbol))
        (p + ys.length) (q + width xs ys) (borrowState (overflow c (pairs xs ys)))) := by
  induction xs generalizing ys c f g p q with
  | nil =>
    induction ys generalizing c f g p q with
    | nil => simp [run, putWord, pairs, padded, width, digits, overflow]
    | cons y ys ih =>
      have hs := column_step c (some y) none (by simp) (putWord f p ((y :: ys).map bitSymbol))
        (putWord g q ([].map bitSymbol)) p q (by rw [List.map_cons, putWord_head]; rfl)
        (by simpa [putWord, inputSymbol] using hg 0 (by simp) (by rw [width_nil_cons]; omega))
      rw [width_nil_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, List.map_nil, shift, ↓reduceIte, reduceCtorEq,
        outputBit, Option.getD_none, Option.getD_some, putWord_nil]
      rw [putWord_cons f]
      have hr := ih (borrowBit c false y) (Function.update f p (bitSymbol y))
        (Function.update g q (bitSymbol (diffBit c false y))) (p + 1) (q + 1)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (ys.length : ℤ) = p + ((y :: ys).length : ℕ) by
            simp; ring]; exact hf)
        (fun j hj hjw => by
          rw [Function.update_of_ne (by omega), show q + 1 + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hg (j + 1) (by simp) (by rw [width_nil_cons]; omega))
      simp only [List.map_nil, putWord_nil] at hr
      rw [hr]
      simp only [pairs_nil_cons, digits, overflow, List.map_cons, putWord_cons, List.length_cons]
      congr 2
      · push_cast; ring
      · push_cast; ring
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hs := column_step c none (some x) (by simp) (putWord f p ([].map bitSymbol))
        (putWord g q ((x :: xs).map bitSymbol)) p q (by simpa [putWord, inputSymbol] using hf)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_cons_nil, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, List.map_nil, shift,
        ↓reduceIte, add_zero, outputBit, Option.getD_none, Option.getD_some]
      have hr := ih (borrowBit c x false) [] f (Function.update g q (bitSymbol (diffBit c x false)))
        p (q + 1) (by simpa using hf)
        (fun j hj hjw => by
          rw [Function.update_of_ne (by omega), show q + 1 + (j : ℤ) = q + ((j + 1 : ℕ) : ℤ) by
            push_cast; ring]
          exact hg (j + 1) (by simpa using hj) (by rw [width_cons_nil]; omega))
      simp only [List.map_nil, putWord_nil] at hr ⊢
      rw [hr]
      simp only [pairs_cons_nil, digits, overflow, List.map_cons, putWord_cons, List.length_nil,
        Nat.cast_zero, add_zero]
      congr 2
      push_cast; ring
    | cons y ys =>
      have hs := column_step c (some y) (some x) (by simp) (putWord f p ((y :: ys).map bitSymbol))
        (putWord g q ((x :: xs).map bitSymbol)) p q (by rw [List.map_cons, putWord_head]; rfl)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_cons_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, shift, ↓reduceIte,
        reduceCtorEq, outputBit, Option.getD_some]
      rw [putWord_cons f]
      have hr := ih (borrowBit c x y) ys (Function.update f p (bitSymbol y))
        (Function.update g q (bitSymbol (diffBit c x y))) (p + 1) (q + 1)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (ys.length : ℤ) = p + ((y :: ys).length : ℕ) by
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

theorem halt (f g : ℤ → Fin (a + 4)) (p q : ℤ) (s : Fin 2) (hf : f p = blank) (hg : g q = blank) :
    step (program a) (cfg f g p q s) = none := by
  simp [step, program, cfg, hf, hg]

theorem diffWord_length (ys xs : List Bool) : (diffWord ys xs).length = width xs ys := by
  rw [diffWord, BinarySub.digits_length, pairs, List.length_zip, padded_left_length,
    padded_right_length, min_self]

/-- Without underflow the minuend holds the exact difference. -/
theorem diffWord_value (ys xs : List Bool) (hle : Counter.value ys ≤ Counter.value xs) :
    Counter.value (diffWord ys xs) = Counter.value xs - Counter.value ys := by
  have h := BinarySub.digits_value_sub (padded xs (width xs ys)) (padded ys (width xs ys))
    (by rw [padded_left_length, padded_right_length])
    (by rw [BinaryPad.padded_value, BinaryPad.padded_value]; exact hle)
  rw [BinaryPad.padded_value, BinaryPad.padded_value] at h
  exact h

/-- Exact execution: scan to the common width and halt. -/
theorem decrease_exact (ys xs : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + ys.length) = blank)
    (hg : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs ys → g (q + j) = blank) :
    run (program a) (width xs ys)
      (cfg (putWord f p (ys.map bitSymbol)) (putWord g q (xs.map bitSymbol)) p q 0) =
      some (cfg (putWord f p (ys.map bitSymbol)) (putWord g q ((diffWord ys xs).map bitSymbol))
        (p + ys.length) (q + width xs ys) (borrowState (overflow false (pairs xs ys)))) ∧
    step (program a) (cfg (putWord f p (ys.map bitSymbol))
      (putWord g q ((diffWord ys xs).map bitSymbol)) (p + ys.length) (q + width xs ys)
      (borrowState (overflow false (pairs xs ys)))) = none := by
  have hr := columns_run false ys xs f g p q hf hg
  rw [show borrowState false = (0 : Fin 2) from rfl] at hr
  refine ⟨hr, halt _ _ _ _ _ ?_ ?_⟩
  · rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
  · rw [putWord_outside _ _ _ _ (Or.inr (by simp [diffWord_length])),
      hg (width xs ys) (Nat.le_max_left _ _) le_rfl]

/-- The in-place subtraction contract: the subtrahend is preserved with its
head parked on its blank end, the minuend holds the modular difference with
its head at the common width. -/
theorem decrease_hoare (ys xs : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hf : f (p + ys.length) = blank)
    (hg : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs ys → g (q + j) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (ys.map bitSymbol)) (putWord g q (xs.map bitSymbol)) p q 0).tapes)
      (fun v => v = (cfg (putWord f p (ys.map bitSymbol))
        (putWord g q ((diffWord ys xs).map bitSymbol)) (p + ys.length) (q + width xs ys) 0).tapes)
      (width xs ys) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := decrease_exact ys xs f g p q hf hg
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.BinaryDecrease
