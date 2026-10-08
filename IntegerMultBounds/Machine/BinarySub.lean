import IntegerMultBounds.Machine.BinaryAdd

/-! Literal least-significant-first modular binary subtraction. The borrow
lives in finite control. Every input column costs exactly one transition. -/

namespace IntegerMultBounds.Machine.BinarySub

variable {a : ℕ}

abbrev bitValue := BinaryAdd.bitValue

def diffBit (borrow x y : Bool) : Bool := Bool.xor (Bool.xor x y) borrow

def borrowBit (borrow x y : Bool) : Bool := (!x && y) || (!x && borrow) || (y && borrow)

theorem full_subtractor (borrow x y : Bool) :
    bitValue x + 2 * bitValue (borrowBit borrow x y) =
      bitValue y + bitValue (diffBit borrow x y) + bitValue borrow := by
  cases borrow <;> cases x <;> cases y <;> decide

def digits : Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | c, (x, y) :: rest => diffBit c x y :: digits (borrowBit c x y) rest

def overflow : Bool → List (Bool × Bool) → Bool
  | c, [] => c
  | c, (x, y) :: rest => overflow (borrowBit c x y) rest

@[simp] theorem digits_length (c : Bool) (columns : List (Bool × Bool)) :
    (digits c columns).length = columns.length := by
  induction columns generalizing c with
  | nil => rfl
  | cons col rest ih => rcases col with ⟨x, y⟩; simp [digits, ih]

/-- Exact arithmetic with incoming and outgoing borrow, without truncating
natural-number subtraction or assuming the minuend is larger. -/
theorem digits_value (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    Counter.value xs + 2 ^ xs.length * bitValue (overflow c (xs.zip ys)) =
      Counter.value ys + Counter.value (digits c (xs.zip ys)) + bitValue c := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [digits, overflow, Counter.value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hi := ih (borrowBit c x y) ys ht
      have ha := full_subtractor c x y
      simp only [List.zip_cons_cons, digits, overflow, Counter.value, List.length_cons,
        pow_succ] at ⊢
      simp only [bitValue, BinaryAdd.bitValue] at ha hi ⊢
      nlinarith

/-- The final control-state borrow detects precisely an unsigned underflow. -/
theorem overflow_eq_true_iff (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    overflow c (xs.zip ys) = true ↔ Counter.value xs < Counter.value ys + bitValue c := by
  have hv := digits_value c xs ys hlen
  have hd := Counter.value_lt (digits c (xs.zip ys))
  have hl : (digits c (xs.zip ys)).length = xs.length := by simp [hlen]
  rw [hl] at hd
  cases hb : overflow c (xs.zip ys) <;> cases c <;>
    simp_all [bitValue, BinaryAdd.bitValue] <;> omega

/-- When no underflow is possible, the output represents ordinary subtraction. -/
theorem digits_value_sub (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hle : Counter.value ys ≤ Counter.value xs) :
    Counter.value (digits false (xs.zip ys)) = Counter.value xs - Counter.value ys := by
  have hv := digits_value false xs ys hlen
  have hb : overflow false (xs.zip ys) = false := by
    have hn := overflow_eq_true_iff false xs ys hlen
    simp only [bitValue, BinaryAdd.bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hn
    cases h : overflow false (xs.zip ys) <;> simp_all
    omega
  simp only [hb, bitValue, BinaryAdd.bitValue, Bool.false_eq_true, ↓reduceIte,
    Nat.mul_zero, Nat.add_zero] at hv
  omega

def borrowState (c : Bool) : Fin 2 := if c then 1 else 0

/-- Scanned source bits and a single control-state borrow determine each
transition. Both source cells are read back unchanged. -/
def program (a : ℕ) : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if (symbols 0 = bitSymbol false ∨ symbols 0 = bitSymbol true) ∧
        (symbols 1 = bitSymbol false ∨ symbols 1 = bitSymbol true) then
      let c := decide (state = 1)
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (borrowState (borrowBit c x y), fun i =>
        (if i = 2 then bitSymbol (diffBit c x y) else symbols i, .right))
    else none

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin 2) : Config 3 2 a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem bit_step (c x y : Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hx : f p = bitSymbol x) (hy : g q = bitSymbol y) :
    step (program a) (cfg f g out p q r (borrowState c)) =
      some (cfg f g (Function.update out r (bitSymbol (diffBit c x y)))
        (p + 1) (q + 1) (r + 1) (borrowState (borrowBit c x y))) := by
  have ht : (program a).transition (borrowState c)
      (fun i => (cfg f g out p q r (borrowState c)).tape i ((cfg f g out p q r (borrowState c)).head i)) =
      some (borrowState (borrowBit c x y), fun i =>
        (if i = 2 then bitSymbol (diffBit c x y)
          else (cfg f g out p q r (borrowState c)).tape i ((cfg f g out p q r (borrowState c)).head i), Move.right)) := by
    cases c <;> cases x <;> cases y <;> simp [program, cfg, borrowState, hx, hy, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

/-- Exactly one transition per source pair; the complete source tapes and all
output cells outside the written word are preserved. -/
theorem columns_run (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    run (program a) xs.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r (borrowState c)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + xs.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) := by
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
      have hr := ih (borrowBit c x y) ys ht (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol y)) (Function.update out r (bitSymbol (diffBit c x y)))
        (p + 1) (q + 1) (r + 1)
      simpa only [← putWord_cons, List.map_cons, List.zip_cons_cons, digits, overflow,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Complete modular subtraction in exactly the common padded width, with
actual halt and final borrow in the control state. -/
theorem sub_exact (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    run (program a) xs.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r (borrowState c)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) ∧
    step (program a)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) = none := by
  constructor
  · simpa only [hlen] using columns_run c xs ys hlen f g out p q r
  · have hx : putWord f p (xs.map (bitSymbol (a := a))) (p + xs.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
    have hy : putWord g q (ys.map (bitSymbol (a := a))) (q + ys.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hg]
    simp [step, program, cfg, hx, hy, blank, bitSymbol]

/-- The final borrow is represented explicitly in the arithmetic witness;
all source and output cells are specified by the tape postcondition. -/
theorem sub_hoare (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r 0).tapes)
      (fun v => ∃ diff : List Bool, ∃ borrow : Bool,
        Counter.value xs + 2 ^ xs.length * bitValue borrow = Counter.value ys + Counter.value diff ∧
        diff.length = xs.length ∧ v =
          (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
            (putWord out r (diff.map bitSymbol)) (p + xs.length) (q + ys.length) (r + xs.length) 0).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := sub_exact false xs ys hlen f g out p q r hf hg
  refine ⟨_, _, le_rfl, hr, hh, digits false (xs.zip ys), overflow false (xs.zip ys), ?_, ?_, rfl⟩
  · simpa [bitValue, BinaryAdd.bitValue] using digits_value false xs ys hlen
  · simp [hlen]

/-- Globally blank-tail output and both complete source words preserved.
Underflow is certified by the final control-state borrow. -/
theorem sub_to_blank (xs ys : List Bool) (hlen : xs.length = ys.length) :
    let diff := digits false (xs.zip ys)
    let borrow := overflow false (xs.zip ys)
    Counter.value xs + 2 ^ xs.length * bitValue borrow = Counter.value ys + Counter.value diff ∧
    diff.length = xs.length ∧
    run (program a) xs.length (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol))
      (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) (wordTape (diff.map bitSymbol))
        xs.length ys.length xs.length (borrowState borrow)) ∧
    step (program a) (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) (wordTape (diff.map bitSymbol))
      xs.length ys.length xs.length (borrowState borrow)) = none := by
  have hw (bits : List Bool) : putWord (fun _ => (blank : Fin (a + 4))) 0 (bits.map bitSymbol) =
      wordTape (bits.map bitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (bits.map bitSymbol)
  obtain ⟨hr, hh⟩ := sub_exact false xs ys hlen (fun _ => (blank : Fin (a + 4)))
    (fun _ => blank) (fun _ => blank) 0 0 0 rfl rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [bitValue, BinaryAdd.bitValue] using digits_value false xs ys hlen
  · simp [hlen]
  · simpa only [hw, zero_add, borrowState, Bool.false_eq_true, ↓reduceIte] using hr
  · simpa only [hw, zero_add] using hh

end IntegerMultBounds.Machine.BinarySub
