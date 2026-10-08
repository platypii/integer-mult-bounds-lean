import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare
import IntegerMultBounds.Machine.Counter

/-! Literal least-significant-first binary addition. Three tapes and three
states suffice for every equally padded input width; carry is finite control.
Each input column costs one transition and a final carry costs one more. -/

namespace IntegerMultBounds.Machine.BinaryAdd

variable {a : ℕ}

def sumBit (carry x y : Bool) : Bool := Bool.xor (Bool.xor x y) carry

def carryBit (carry x y : Bool) : Bool := (x && y) || (x && carry) || (y && carry)

def bitValue (b : Bool) : ℕ := if b then 1 else 0

theorem full_adder (carry x y : Bool) :
    bitValue (sumBit carry x y) + 2 * bitValue (carryBit carry x y) =
      bitValue x + bitValue y + bitValue carry := by
  cases carry <;> cases x <;> cases y <;> decide

def digits : Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | c, (x, y) :: rest => sumBit c x y :: digits (carryBit c x y) rest

def overflow : Bool → List (Bool × Bool) → Bool
  | c, [] => c
  | c, (x, y) :: rest => overflow (carryBit c x y) rest

def carryWord (c : Bool) : List Bool := if c then [true] else []

def result (c : Bool) (columns : List (Bool × Bool)) : List Bool :=
  digits c columns ++ carryWord (overflow c columns)

@[simp] theorem digits_length (c : Bool) (columns : List (Bool × Bool)) :
    (digits c columns).length = columns.length := by
  induction columns generalizing c with
  | nil => rfl
  | cons col rest ih => rcases col with ⟨x, y⟩; simp [digits, ih]

@[simp] theorem result_cons (c x y : Bool) (columns : List (Bool × Bool)) :
    result c ((x, y) :: columns) = sumBit c x y :: result (carryBit c x y) columns := rfl

/-- The complete LSF output represents exact addition, including final carry. -/
theorem result_value (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    Counter.value (result c (xs.zip ys)) = Counter.value xs + Counter.value ys + bitValue c := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    cases c <;> simp [result, digits, overflow, carryWord, Counter.value, bitValue]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      simp only [List.zip_cons_cons, result_cons, Counter.value]
      rw [ih _ _ ht]
      have ha := full_adder c x y
      simp only [bitValue] at ha ⊢
      omega

theorem result_length (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (result c (xs.zip ys)).length = xs.length + (carryWord (overflow c (xs.zip ys))).length := by
  simp [result, hlen]

theorem result_length_le (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (result c (xs.zip ys)).length ≤ xs.length + 1 := by
  rw [result_length c xs ys hlen]
  cases overflow c (xs.zip ys) <;> simp [carryWord]

def carryState (c : Bool) : Fin 3 := if c then 1 else 0

def finalState (c : Bool) : Fin 3 := if c then 2 else 0

/-- Only the scanned symbols determine the sum and next carry. No integer
arithmetic or unbounded register appears in this transition table. -/
def program (a : ℕ) : Program 3 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 2 then none
    else if symbols 0 = blank ∧ symbols 1 = blank then
      if state = 1 then some (2, fun i =>
        if i = 2 then (bitSymbol true, .right) else (symbols i, .stay)) else none
    else if (symbols 0 = bitSymbol false ∨ symbols 0 = bitSymbol true) ∧
        (symbols 1 = bitSymbol false ∨ symbols 1 = bitSymbol true) then
      let c := decide (state = 1)
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (carryState (carryBit c x y), fun i =>
        (if i = 2 then bitSymbol (sumBit c x y) else symbols i, .right))
    else none

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin 3) : Config 3 3 a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem bit_step (c x y : Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hx : f p = bitSymbol x) (hy : g q = bitSymbol y) :
    step (program a) (cfg f g out p q r (carryState c)) =
      some (cfg f g (Function.update out r (bitSymbol (sumBit c x y)))
        (p + 1) (q + 1) (r + 1) (carryState (carryBit c x y))) := by
  have ht : (program a).transition (carryState c)
      (fun i => (cfg f g out p q r (carryState c)).tape i ((cfg f g out p q r (carryState c)).head i)) =
      some (carryState (carryBit c x y), fun i =>
        (if i = 2 then bitSymbol (sumBit c x y)
          else (cfg f g out p q r (carryState c)).tape i ((cfg f g out p q r (carryState c)).head i), Move.right)) := by
    cases c <;> cases x <;> cases y <;> simp [program, cfg, carryState, hx, hy, blank, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

private theorem final_carry_step (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    step (program a) (cfg f g out p q r 1) =
      some (cfg f g (Function.update out r (bitSymbol true)) p q (r + 1) 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, hf, hg, and_self,
    Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm, hf, hg] <;> intro hj <;> subst j <;> assumption

/-- Exactly one transition for each pair of source digits. Both sources are
preserved as complete tapes, with arbitrary untouched background contents. -/
theorem columns_run (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    run (program a) xs.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r (carryState c)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + xs.length) (r + xs.length) (carryState (overflow c (xs.zip ys)))) := by
  induction xs generalizing ys c f g out p q r with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [run, digits, overflow, putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hs := bit_step c x y (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ((y :: ys).map bitSymbol)) out p q r
        (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
      simp only [List.length_cons, run, hs, Option.bind_some]
      have hr := ih (carryBit c x y) ys ht (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol y)) (Function.update out r (bitSymbol (sumBit c x y)))
        (p + 1) (q + 1) (r + 1)
      simpa only [← putWord_cons, List.map_cons, List.zip_cons_cons, digits, overflow,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

private theorem finish_exact (c : Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    run (program a) (carryWord c).length (cfg f g out p q r (carryState c)) =
      some (cfg f g (putWord out r ((carryWord c).map bitSymbol))
        p q (r + (carryWord c).length) (finalState c)) ∧
    step (program a) (cfg f g (putWord out r ((carryWord c).map bitSymbol))
      p q (r + (carryWord c).length) (finalState c)) = none := by
  cases c with
  | false => simp [carryWord, carryState, finalState, run, step, program, cfg, putWord, hf, hg]
  | true =>
    constructor
    · simpa only [carryWord, carryState, finalState, ↓reduceIte, List.length_singleton,
        List.map_cons, List.map_nil, putWord, run_one, Nat.cast_one] using final_carry_step f g out p q r hf hg
    · simp [carryWord, finalState, step, program, cfg]

/-- Complete addition with exact runtime equal to the number of written output
bits. The optional final carry is charged, and the machine actually halts. -/
theorem add_exact (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    run (program a) (result c (xs.zip ys)).length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r (carryState c)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((result c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + (result c (xs.zip ys)).length)
        (finalState (overflow c (xs.zip ys)))) ∧
    step (program a)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((result c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + (result c (xs.zip ys)).length)
        (finalState (overflow c (xs.zip ys)))) = none := by
  have hd : ((digits c (xs.zip ys)).map (bitSymbol (a := a))).length = xs.length := by
    simp [hlen]
  have hword : putWord (putWord out r ((digits c (xs.zip ys)).map bitSymbol)) (r + xs.length)
      ((carryWord (overflow c (xs.zip ys))).map bitSymbol) =
      putWord out r ((result c (xs.zip ys)).map bitSymbol) := by
    rw [← hd, putWord_append_forward, ← List.map_append]
    rfl
  have hr := columns_run c xs ys hlen f g out p q r
  have he := finish_exact (overflow c (xs.zip ys)) (putWord f p (xs.map bitSymbol))
    (putWord g q (ys.map bitSymbol)) (putWord out r ((digits c (xs.zip ys)).map bitSymbol))
    (p + xs.length) (q + xs.length) (r + xs.length)
    (by rw [putWord_outside _ _ _ _ (Or.inr (by simp))]; exact hf)
    (by rw [hlen, putWord_outside _ _ _ _ (Or.inr (by simp))]; exact hg)
  rw [hword] at he
  have hp : r + (xs.length : ℤ) + (carryWord (overflow c (xs.zip ys))).length =
      r + (result c (xs.zip ys)).length := by rw [result_length c xs ys hlen]; push_cast; omega
  rw [hp] at he
  refine ⟨?_, by simpa only [hlen] using he.2⟩
  rw [result_length c xs ys hlen, run_add, hr]
  simp only [Option.bind_some]
  simpa only [result_length c xs ys hlen, hlen] using he.1

/-- Starting without an incoming carry, the output is the exact sum and the
transition count is at most one more than the common padded source width. -/
theorem add_hoare (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r 0).tapes)
      (fun v => ∃ sum : List Bool, Counter.value sum = Counter.value xs + Counter.value ys ∧
        sum.length ≤ xs.length + 1 ∧ v =
          (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
            (putWord out r (sum.map bitSymbol)) (p + xs.length) (q + ys.length) (r + sum.length) 0).tapes)
      (xs.length + 1) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := add_exact false xs ys hlen f g out p q r hf hg
  refine ⟨_, _, result_length_le false xs ys hlen, hr, hh, result false (xs.zip ys), ?_,
    result_length_le false xs ys hlen, rfl⟩
  simpa only [bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using result_value false xs ys hlen

/-- Blank output initialization produces a globally blank-tail word, with both
entire input tapes preserved. This is an executable addition, not a cost oracle. -/
theorem add_to_blank (xs ys : List Bool) (hlen : xs.length = ys.length) :
    let sum := result false (xs.zip ys)
    Counter.value sum = Counter.value xs + Counter.value ys ∧ sum.length ≤ xs.length + 1 ∧
    run (program a) sum.length (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol))
      (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) (wordTape (sum.map bitSymbol))
        xs.length ys.length sum.length (finalState (overflow false (xs.zip ys)))) ∧
    step (program a) (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) (wordTape (sum.map bitSymbol))
      xs.length ys.length sum.length (finalState (overflow false (xs.zip ys)))) = none := by
  have hw (bits : List Bool) : putWord (fun _ => (blank : Fin (a + 4))) 0 (bits.map bitSymbol) =
      wordTape (bits.map bitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (bits.map bitSymbol)
  obtain ⟨hr, hh⟩ := add_exact false xs ys hlen (fun _ => (blank : Fin (a + 4)))
    (fun _ => blank) (fun _ => blank) 0 0 0 rfl rfl
  refine ⟨?_, result_length_le false xs ys hlen, ?_, ?_⟩
  · simpa only [bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using result_value false xs ys hlen
  · simpa only [hw, zero_add, carryState, Bool.false_eq_true, ↓reduceIte] using hr
  · simpa only [hw, zero_add] using hh

end IntegerMultBounds.Machine.BinaryAdd
