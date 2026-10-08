import IntegerMultBounds.Machine.BinaryPad

/-! Literal least-significant-first binary comparison. Three tapes and four
states: the two operands are scanned forward together, with a missing high
bit read as zero, and the order so far lives in finite control, a later
column overriding every earlier one. On the common blank the result bit,
whether the first operand is strictly smaller, is written on the third tape.
Both operands are preserved; the cost is the larger width plus one. -/

namespace IntegerMultBounds.Machine.BinaryCompare

variable {a : ℕ}

open BinaryPad (columns inputSymbol outputBit padded)

/-- The order after one more, more significant, column. -/
def cmpBit (o : Ordering) (x y : Bool) : Ordering :=
  if x = y then o else if x then .gt else .lt

/-- The order of two words from an initial order, least significant column first. -/
def rel : Ordering → List (Bool × Bool) → Ordering
  | o, [] => o
  | o, (x, y) :: rest => rel (cmpBit o x y) rest

theorem rel_eq (o : Ordering) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    rel o (xs.zip ys) = if Counter.value xs < Counter.value ys then .lt
      else if Counter.value ys < Counter.value xs then .gt else o := by
  induction xs generalizing ys o with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [rel, Counter.value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      simp only [List.zip_cons_cons, rel, ih _ _ ht]
      cases x <;> cases y <;> simp only [cmpBit, Counter.value, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte] <;>
        split_ifs <;> first | rfl | omega

theorem rel_lt (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (rel .eq (xs.zip ys) = .lt) = (Counter.value xs < Counter.value ys) := by
  rw [rel_eq _ _ _ hlen]
  split_ifs <;> simp <;> omega

/-- The finite control: zero for equal so far, one for smaller, two for
larger, three after writing the result. -/
def ordState : Ordering → Fin 4
  | .eq => 0
  | .lt => 1
  | .gt => 2

def stateOrd (s : Fin 4) : Ordering := if s = 0 then .eq else if s = 1 then .lt else .gt

/-- A source cell is blank or a bit; blank reads as zero. -/
def isInput (x : Fin (a + 4)) : Prop := x = blank ∨ x = bitSymbol false ∨ x = bitSymbol true

instance (x : Fin (a + 4)) : Decidable (isInput x) := by unfold isInput; infer_instance

/-- Each operand head advances only over its own bits and parks on its blank
end; the output head stays until the result is written. -/
def program (a : ℕ) : Program 3 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 3 then none
    else if symbols 0 = blank ∧ symbols 1 = blank then
      some (3, fun i => if i = 2 then (bitSymbol (decide (state = 1)), .right) else (symbols i, .stay))
    else if isInput (symbols 0) ∧ isInput (symbols 1) then
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (ordState (cmpBit (stateOrd state) x y), fun i =>
        (symbols i, if i = 2 then .stay else if symbols i = blank then .stay else .right))
    else none

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin 4) : Config 3 4 a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

/-- A head moves only over an actual bit. -/
def shift (x : Option Bool) : ℤ := if x = none then 0 else 1

private theorem column_step (o : Ordering) (x y : Option Bool) (hv : x ≠ none ∨ y ≠ none)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = inputSymbol y) :
    step (program a) (cfg f g out p q r (ordState o)) =
      some (cfg f g out (p + shift x) (q + shift y) r
        (ordState (cmpBit o (outputBit x) (outputBit y)))) := by
  have ht : (program a).transition (ordState o)
      (fun i => (cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i)) =
      some (ordState (cmpBit o (outputBit x) (outputBit y)), fun i =>
        ((cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i),
          if i = 2 then Move.stay else if i = 0 then (if x = none then Move.stay else Move.right)
          else (if y = none then Move.stay else Move.right))) := by
    cases o <;> rcases x with _ | x <;> rcases y with _ | y <;> simp at hv <;>
      (try cases x) <;> (try cases y) <;>
      simp [program, cfg, ordState, stateOrd, cmpBit, isInput, hx, hy, inputSymbol, outputBit,
        blank, bitSymbol]
    all_goals (funext i; fin_cases i <;> simp [hx, hy, inputSymbol, blank, bitSymbol])
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rcases x with _ | x <;> rcases y with _ | y <;> simp [shift]
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

/-- The common width of two operands. -/
def width (xs ys : List Bool) : ℕ := max xs.length ys.length

/-- The aligned columns of the operands, read as bits. -/
def pairs (xs ys : List Bool) : List (Bool × Bool) :=
  (padded xs (width xs ys)).zip (padded ys (width xs ys))

theorem padded_left_length (xs ys : List Bool) :
    (padded xs (width xs ys)).length = width xs ys :=
  BinaryPad.padded_length _ _ (Nat.le_max_left _ _)

theorem padded_right_length (xs ys : List Bool) :
    (padded ys (width xs ys)).length = width xs ys :=
  BinaryPad.padded_length _ _ (Nat.le_max_right _ _)

theorem pairs_cons_cons (x y : Bool) (xs ys : List Bool) :
    pairs (x :: xs) (y :: ys) = (x, y) :: pairs xs ys := by
  simp [pairs, padded, width, List.length_cons, max_add_add_right, Nat.add_sub_add_right]

theorem pairs_nil_cons (y : Bool) (ys : List Bool) :
    pairs [] (y :: ys) = (false, y) :: pairs [] ys := by
  simp [pairs, padded, width, List.replicate_succ]

theorem pairs_cons_nil (x : Bool) (xs : List Bool) :
    pairs (x :: xs) [] = (x, false) :: pairs xs [] := by
  simp [pairs, padded, width, List.replicate_succ]

theorem width_cons_cons (x y : Bool) (xs ys : List Bool) :
    width (x :: xs) (y :: ys) = width xs ys + 1 := by
  simp [width, max_add_add_right]

theorem width_nil_cons (y : Bool) (ys : List Bool) : width [] (y :: ys) = width [] ys + 1 := by
  simp [width]

theorem width_cons_nil (x : Bool) (xs : List Bool) : width (x :: xs) [] = width xs [] + 1 := by
  simp [width]

/-- One transition per aligned column; every cell of all three tapes is
retained and each operand head parks on its own blank end. -/
theorem columns_run (o : Ordering) (xs ys : List Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    run (program a) (width xs ys)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r (ordState o)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out
        (p + xs.length) (q + ys.length) r (ordState (rel o (pairs xs ys)))) := by
  induction xs generalizing ys o f g p q with
  | nil =>
    induction ys generalizing o g q with
    | nil => simp [run, putWord, pairs, padded, width, rel]
    | cons y ys ih =>
      have hs := column_step o none (some y) (by simp) (putWord f p ([].map bitSymbol))
        (putWord g q ((y :: ys).map bitSymbol)) out p q r (by simpa [putWord, inputSymbol] using hf)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_nil_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, List.map_nil, shift, ↓reduceIte, add_zero,
        reduceCtorEq, outputBit, Option.getD_none, Option.getD_some]
      rw [putWord_cons g]
      have hr := ih (cmpBit o false y) (Function.update g q (bitSymbol y)) (q + 1)
        (by rw [Function.update_of_ne (by omega), show q + 1 + (ys.length : ℤ) = q + ((y :: ys).length : ℕ) by
            simp; ring]; exact hg)
      simp only [List.map_nil] at hr
      rw [hr]
      simp only [pairs_nil_cons, rel, List.length_cons, List.length_nil, Nat.cast_zero, add_zero]
      congr 2
      push_cast; ring
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hs := column_step o (some x) none (by simp) (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ([].map bitSymbol)) out p q r (by rw [List.map_cons, putWord_head]; rfl)
        (by simpa [putWord, inputSymbol] using hg)
      rw [width_cons_nil, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, List.map_nil, shift, ↓reduceIte, add_zero,
        reduceCtorEq, outputBit, Option.getD_none, Option.getD_some]
      rw [putWord_cons f]
      have hr := ih (cmpBit o x false) [] (Function.update f p (bitSymbol x)) g (p + 1) q
        (by rw [Function.update_of_ne (by omega), show p + 1 + (xs.length : ℤ) = p + ((x :: xs).length : ℕ) by
            simp; ring]; exact hf) hg
      simp only [List.map_nil] at hr
      rw [hr]
      simp only [pairs_cons_nil, rel, List.length_cons, List.length_nil, Nat.cast_zero, add_zero]
      congr 2
      push_cast; ring
    | cons y ys =>
      have hs := column_step o (some x) (some y) (by simp) (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ((y :: ys).map bitSymbol)) out p q r (by rw [List.map_cons, putWord_head]; rfl)
        (by rw [List.map_cons, putWord_head]; rfl)
      rw [width_cons_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, shift, ↓reduceIte, reduceCtorEq, outputBit,
        Option.getD_some]
      rw [putWord_cons f, putWord_cons g]
      have hr := ih (cmpBit o x y) ys (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol y)) (p + 1) (q + 1)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (xs.length : ℤ) = p + ((x :: xs).length : ℕ) by
            simp; ring]; exact hf)
        (by rw [Function.update_of_ne (by omega), show q + 1 + (ys.length : ℤ) = q + ((y :: ys).length : ℕ) by
            simp; ring]; exact hg)
      rw [hr]
      simp only [pairs_cons_cons, rel, List.length_cons]
      congr 2
      · push_cast; ring
      · push_cast; ring

private theorem final_step (o : Ordering) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    step (program a) (cfg f g out p q r (ordState o)) =
      some (cfg f g (Function.update out r (bitSymbol (decide (o = .lt)))) p q (r + 1) 3) := by
  have ht : (program a).transition (ordState o)
      (fun i => (cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i)) =
      some (3, fun i => if i = 2 then (bitSymbol (decide (o = .lt)), Move.right)
        else ((cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i),
          Move.stay)) := by
    cases o <;> simp [program, cfg, ordState, hf, hg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

theorem halt (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    step (program a) (cfg f g out p q r 3) = none := by
  simp [step, program, cfg]

/-- The result word: one bit, whether the first operand is strictly smaller. -/
def resultWord (xs ys : List Bool) : List (Fin (a + 4)) :=
  [bitSymbol (decide (Counter.value xs < Counter.value ys))]

theorem rel_pairs_lt (xs ys : List Bool) :
    decide (rel .eq (pairs xs ys) = .lt) = decide (Counter.value xs < Counter.value ys) := by
  apply decide_eq_decide.mpr
  rw [← BinaryPad.padded_value xs (width xs ys), ← BinaryPad.padded_value ys (width xs ys)]
  exact iff_of_eq (rel_lt _ _ (by rw [padded_left_length, padded_right_length]))

/-- Exact execution: scan to the common width, write the result bit, halt. -/
theorem compare_exact (xs ys : List Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    run (program a) (width xs ys + 1)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r 0) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + xs.length) (q + ys.length) (r + 1) 3) ∧
    step (program a) (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + xs.length) (q + ys.length) (r + 1) 3) = none := by
  refine ⟨?_, halt _ _ _ _ _ _⟩
  have hr := columns_run .eq xs ys f g out p q r hf hg
  rw [show ordState .eq = (0 : Fin 4) from rfl] at hr
  have hblankf : putWord f p (xs.map bitSymbol) (p + xs.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
  have hblankg : putWord g q (ys.map bitSymbol) (q + ys.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hg]
  have hfin := final_step (rel .eq (pairs xs ys)) (putWord f p (xs.map bitSymbol))
    (putWord g q (ys.map bitSymbol)) out (p + xs.length) (q + ys.length) r hblankf hblankg
  rw [run_add, hr]
  simp only [Option.bind_some, run_one, hfin, rel_pairs_lt, resultWord, putWord]

/-- The comparison contract: both operands are preserved with their heads
parked on their blank ends, and the result bit is written at the output head. -/
theorem compare_hoare (xs ys : List Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out
        p q r 0).tapes)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + xs.length) (q + ys.length) (r + 1) 0).tapes)
      (width xs ys + 1) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := compare_exact xs ys f g out p q r hf hg
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.BinaryCompare
