import IntegerMultBounds.Machine.BinaryAdd
import IntegerMultBounds.Machine.BinarySub

/-! A generic three-tape column transducer on equally padded
least-significant-first words: a finite control reads one bit from each
operand, writes one output bit and moves on, halting on the common blank.
Modular addition and bitwise exclusive or are instances; each costs exactly
the common width and preserves both operands. -/

namespace IntegerMultBounds.Machine.ColumnTransducer

variable {a s : ℕ}

/-- The output and next state for each control state and column. -/
structure Rule (s : ℕ) where
  out : Fin (s + 1) → Bool → Bool → Bool
  next : Fin (s + 1) → Bool → Bool → Fin (s + 1)

/-- The output bits of a rule from a state over the columns. -/
def digits (R : Rule s) : Fin (s + 1) → List (Bool × Bool) → List Bool
  | _, [] => []
  | st, (x, y) :: rest => R.out st x y :: digits R (R.next st x y) rest

@[simp] theorem digits_length (R : Rule s) (st : Fin (s + 1)) (cols : List (Bool × Bool)) :
    (digits R st cols).length = cols.length := by
  induction cols generalizing st with
  | nil => rfl
  | cons col rest ih => rcases col with ⟨x, y⟩; simp [digits, ih]

/-- Halt on the common blank; otherwise transduce one column. -/
def program (R : Rule s) (a : ℕ) : Program 3 (s + 1) a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if (symbols 0 = bitSymbol false ∨ symbols 0 = bitSymbol true) ∧
        (symbols 1 = bitSymbol false ∨ symbols 1 = bitSymbol true) then
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (R.next state x y, fun i =>
        (if i = 2 then bitSymbol (R.out state x y) else symbols i, .right))
    else none

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin (s + 1)) : Config 3 (s + 1) a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem bit_step (R : Rule s) (st : Fin (s + 1)) (x y : Bool)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (hx : f p = bitSymbol x) (hy : g q = bitSymbol y) :
    step (program R a) (cfg f g out p q r st) =
      some (cfg f g (Function.update out r (bitSymbol (R.out st x y)))
        (p + 1) (q + 1) (r + 1) (R.next st x y)) := by
  have ht : (program R a).transition st
      (fun i => (cfg f g out p q r st).tape i ((cfg f g out p q r st).head i)) =
      some (R.next st x y, fun i =>
        (if i = 2 then bitSymbol (R.out st x y)
          else (cfg f g out p q r st).tape i ((cfg f g out p q r st).head i), Move.right)) := by
    cases x <;> cases y <;> simp [program, cfg, hx, hy, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

/-- The control state after the columns. -/
def foldState (R : Rule s) : Fin (s + 1) → List (Bool × Bool) → Fin (s + 1)
  | st, [] => st
  | st, (x, y) :: rest => foldState R (R.next st x y) rest

/-- Exactly one transition per column; both sources are retained entirely. -/
theorem columns_run (R : Rule s) (st : Fin (s + 1)) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    run (program R a) xs.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r st) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits R st (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + xs.length) (r + xs.length) (foldState R st (xs.zip ys))) := by
  induction xs generalizing ys st f g out p q r with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [run, digits, foldState, putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hs := bit_step R st x y (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ((y :: ys).map bitSymbol)) out p q r
        (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
      simp only [List.length_cons, run, hs, Option.bind_some]
      have hr := ih (R.next st x y) ys ht (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol y)) (Function.update out r (bitSymbol (R.out st x y)))
        (p + 1) (q + 1) (r + 1)
      simpa only [← putWord_cons, List.map_cons, List.zip_cons_cons, digits, foldState,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Complete execution in exactly the common width, with actual halt. -/
theorem transduce_exact (R : Rule s) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    run (program R a) xs.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r 0) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits R 0 (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + xs.length) (foldState R 0 (xs.zip ys))) ∧
    step (program R a)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits R 0 (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + xs.length) (foldState R 0 (xs.zip ys))) = none := by
  constructor
  · simpa only [hlen] using columns_run R 0 xs ys hlen f g out p q r
  · have hx : putWord f p (xs.map (bitSymbol (a := a))) (p + xs.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
    have hy : putWord g q (ys.map (bitSymbol (a := a))) (q + ys.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hg]
    simp [step, program, cfg, hx, hy, blank, bitSymbol]

/-- The transducer contract: both operands preserved, the output word written
at the output head, every head advanced by the common width. -/
theorem transduce_hoare (R : Rule s) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (q + ys.length) = blank) :
    HoareTime (program R a)
      (fun v => v = (cfg (s := s) (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        out p q r 0).tapes)
      (fun v => v = (cfg (s := s) (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((digits R 0 (xs.zip ys)).map bitSymbol))
        (p + xs.length) (q + ys.length) (r + xs.length) 0).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := transduce_exact R xs ys hlen f g out p q r hf hg
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

theorem value_append (xs ys : List Bool) :
    Counter.value (xs ++ ys) = Counter.value xs + 2 ^ xs.length * Counter.value ys := by
  induction xs with
  | nil => simp [Counter.value]
  | cons x xs ih => simp [Counter.value, ih, pow_succ]; ring

section AddMod

/-- Modular addition: state one carries. -/
def addRule : Rule 1 where
  out := fun st x y => BinaryAdd.sumBit (decide (st = 1)) x y
  next := fun st x y => BinarySub.borrowState (BinaryAdd.carryBit (decide (st = 1)) x y)

theorem addRule_digits (c : Bool) (cols : List (Bool × Bool)) :
    digits addRule (BinarySub.borrowState c) cols = BinaryAdd.digits c cols := by
  induction cols generalizing c with
  | nil => rfl
  | cons col rest ih =>
    rcases col with ⟨x, y⟩
    have hc : decide (BinarySub.borrowState c = (1 : Fin 2)) = c := by
      cases c <;> simp [BinarySub.borrowState]
    simp only [digits, BinaryAdd.digits]
    rw [show addRule.out (BinarySub.borrowState c) x y = BinaryAdd.sumBit c x y by simp [addRule, hc],
      show addRule.next (BinarySub.borrowState c) x y = BinarySub.borrowState (BinaryAdd.carryBit c x y) by
        simp [addRule, hc], ih]

/-- The sum modulo two to the common width. -/
theorem addRule_value (xs ys : List Bool) (hlen : xs.length = ys.length) :
    Counter.value (digits addRule 0 (xs.zip ys)) =
      (Counter.value xs + Counter.value ys) % 2 ^ xs.length := by
  have h0 : (0 : Fin 2) = BinarySub.borrowState false := rfl
  rw [h0, addRule_digits]
  have hv := BinaryAdd.result_value false xs ys hlen
  simp only [BinaryAdd.result, value_append, BinaryAdd.digits_length, List.length_zip, ← hlen,
    min_self, BinaryAdd.bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hv
  have hd := Counter.value_lt (BinaryAdd.digits false (xs.zip ys))
  rw [BinaryAdd.digits_length, List.length_zip, ← hlen, min_self] at hd
  rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

end AddMod

section Xor

/-- Bitwise exclusive or: a single control state. -/
def xorRule : Rule 0 where
  out := fun _ x y => xor x y
  next := fun st _ _ => st

theorem xorRule_digits (st : Fin 1) (cols : List (Bool × Bool)) :
    digits xorRule st cols = cols.map fun c => xor c.1 c.2 := by
  induction cols generalizing st with
  | nil => rfl
  | cons col rest ih =>
    rcases col with ⟨x, y⟩
    simp only [digits, List.map_cons]
    rw [show xorRule.out st x y = xor x y from rfl, show xorRule.next st x y = st from rfl, ih]

end Xor

end IntegerMultBounds.Machine.ColumnTransducer
