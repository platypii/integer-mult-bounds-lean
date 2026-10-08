import IntegerMultBounds.Machine.RadixDigits
import IntegerMultBounds.Machine.Hoare

/-! Literal least-significant-first modular fixed-radix subtraction. The borrow
lives in finite control. Every input column costs exactly one transition. -/

namespace IntegerMultBounds.Machine.RadixSub

variable {q : ℕ}
open RadixDigits

def bitValue (b : Bool) : ℕ := if b then 1 else 0

def borrowDigit (borrow : Bool) (x y : Fin q) : Bool :=
  if x.val < y.val + bitValue borrow then true else false

def diffDigit (borrow : Bool) (x y : Fin q) : Fin q :=
  if h : x.val < y.val + bitValue borrow then
    ⟨q + x.val - y.val - bitValue borrow, by
      have hx := x.isLt
      have hy := y.isLt
      cases borrow <;> simp [bitValue] at * <;> omega⟩
  else
    ⟨x.val - y.val - bitValue borrow, by
      have hx := x.isLt
      omega⟩

theorem full_subtractor (borrow : Bool) (x y : Fin q) :
    x.val + q * bitValue (borrowDigit borrow x y) =
      y.val + (diffDigit borrow x y).val + bitValue borrow := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.val < y.val + bitValue borrow
  · have hb : borrowDigit borrow x y = true := by simp only [borrowDigit,h,ite_true]
    have hd : (diffDigit borrow x y).val = q + x.val - y.val - bitValue borrow := by
      simp only [diffDigit,h,dite_true]
    rw [hb,hd]
    cases borrow <;> simp_all [bitValue] <;> omega
  · have hb : borrowDigit borrow x y = false := by simp only [borrowDigit,h,ite_false]
    have hd : (diffDigit borrow x y).val = x.val - y.val - bitValue borrow := by
      simp only [diffDigit,h,dite_false]
    rw [hb,hd]
    cases borrow <;> simp_all [bitValue]
    omega

def digits : Bool → List (Fin q × Fin q) → List (Fin q)
  | _, [] => []
  | c, (x, y) :: rest => diffDigit c x y :: digits (borrowDigit c x y) rest

def overflow : Bool → List (Fin q × Fin q) → Bool
  | c, [] => c
  | c, (x, y) :: rest => overflow (borrowDigit c x y) rest

@[simp] theorem digits_length (c : Bool) (columns : List (Fin q × Fin q)) :
    (digits c columns).length = columns.length := by
  induction columns generalizing c with
  | nil => rfl
  | cons col rest ih => rcases col with ⟨x, y⟩; simp [digits, ih]

/-- Exact arithmetic with incoming and outgoing borrow, without truncating
natural-number subtraction or assuming the minuend is larger. -/
theorem digits_value (c : Bool) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    value xs + q ^ xs.length * bitValue (overflow c (xs.zip ys)) =
      value ys + value (digits c (xs.zip ys)) + bitValue c := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [digits, overflow, value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hi := ih (borrowDigit c x y) ys ht
      have ha := full_subtractor c x y
      simp only [List.zip_cons_cons, digits, overflow, value, List.length_cons,
        pow_succ] at ⊢
      simp only [bitValue] at ha hi ⊢
      nlinarith

/-- The fixed-width output is the canonical modular difference, including an
incoming borrow. One modulus is enough because both operands fit the width. -/
theorem digits_value_mod (hq : 2 ≤ q) (c : Bool) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) :
    value (digits c (xs.zip ys)) =
      (q ^ xs.length + value xs - value ys - bitValue c) % q ^ xs.length := by
  have hv := digits_value c xs ys hlen
  have hd : value (digits c (xs.zip ys)) < q ^ xs.length := by
    simpa [hlen] using value_lt hq (digits c (xs.zip ys))
  cases hb : overflow c (xs.zip ys) with
  | false =>
    simp only [hb,bitValue,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at hv
    have hr : q ^ xs.length + value xs - value ys - bitValue c =
        q ^ xs.length + value (digits c (xs.zip ys)) := by
      dsimp only [bitValue]
      omega
    rw [hr,Nat.add_mod]
    simp [Nat.mod_eq_of_lt hd]
  | true =>
    simp only [hb,bitValue,ite_true,Nat.mul_one] at hv
    have hr : q ^ xs.length + value xs - value ys - bitValue c =
        value (digits c (xs.zip ys)) := by
      dsimp only [bitValue]
      omega
    rw [hr,Nat.mod_eq_of_lt hd]

/-- The final control-state borrow detects precisely an unsigned underflow. -/
theorem overflow_eq_true_iff (hq : 2 ≤ q) (c : Bool) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    overflow c (xs.zip ys) = true ↔ value xs < value ys + bitValue c := by
  have hv := digits_value c xs ys hlen
  have hd := value_lt hq (digits c (xs.zip ys))
  have hl : (digits c (xs.zip ys)).length = xs.length := by simp [hlen]
  rw [hl] at hd
  cases hb : overflow c (xs.zip ys) <;> cases c <;>
    simp_all [bitValue] <;> omega

/-- When no underflow is possible, the output represents ordinary subtraction. -/
theorem digits_value_sub (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length)
    (hle : value ys ≤ value xs) :
    value (digits false (xs.zip ys)) = value xs - value ys := by
  have hv := digits_value false xs ys hlen
  have hb : overflow false (xs.zip ys) = false := by
    have hn := overflow_eq_true_iff hq false xs ys hlen
    simp only [bitValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hn
    cases h : overflow false (xs.zip ys) <;> simp_all
    omega
  simp only [hb, bitValue, Bool.false_eq_true, ↓reduceIte,
    Nat.mul_zero, Nat.add_zero] at hv
  omega

def borrowState (c : Bool) : Fin 2 := if c then 1 else 0

/-- Scanned source digits and a single control-state borrow determine each
transition. Both source cells are read back unchanged. -/
def program (q : ℕ) : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    match readDigit (symbols 0), readDigit (symbols 1) with
    | some x, some y =>
      let c := decide (state = 1)
      some (borrowState (borrowDigit c x y), fun i =>
        (if i = 2 then digitSymbol (diffDigit c x y) else symbols i, .right))
    | _, _ => none

def cfg (f g out : ℤ → Fin (q + 4)) (p s r : ℤ) (state : Fin 2) : Config 3 2 q where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then s else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem digit_step (c : Bool) (x y : Fin q) (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hx : f p = digitSymbol x) (hy : g s = digitSymbol y) :
    step (program q) (cfg f g out p s r (borrowState c)) =
      some (cfg f g (Function.update out r (digitSymbol (diffDigit c x y)))
        (p + 1) (s + 1) (r + 1) (borrowState (borrowDigit c x y))) := by
  have ht : (program q).transition (borrowState c)
      (fun i => (cfg f g out p s r (borrowState c)).tape i ((cfg f g out p s r (borrowState c)).head i)) =
      some (borrowState (borrowDigit c x y), fun i =>
        (if i = 2 then digitSymbol (diffDigit c x y)
          else (cfg f g out p s r (borrowState c)).tape i ((cfg f g out p s r (borrowState c)).head i), Move.right)) := by
    cases c <;> simp [program, cfg, borrowState, hx, hy, readDigit_symbol]
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
theorem columns_run (c : Bool) (xs ys : List (Fin q)) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (q + 4)) (p s r : ℤ) :
    run (program q) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r (borrowState c)) =
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + xs.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) := by
  induction xs generalizing ys c f g out p s r with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [run, digits, overflow, putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hs := digit_step c x y (putWord f p ((x :: xs).map digitSymbol))
        (putWord g s ((y :: ys).map digitSymbol)) out p s r
        (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
      simp only [List.length_cons, run, hs, Option.bind_some]
      have hr := ih (borrowDigit c x y) ys ht (Function.update f p (digitSymbol x))
        (Function.update g s (digitSymbol y)) (Function.update out r (digitSymbol (diffDigit c x y)))
        (p + 1) (s + 1) (r + 1)
      simpa only [← putWord_cons, List.map_cons, List.zip_cons_cons, digits, overflow,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Complete modular subtraction in exactly the common padded width, with
actual halt and final borrow in the control state. -/
theorem sub_exact (c : Bool) (xs ys : List (Fin q)) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (s + ys.length) = blank) :
    run (program q) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r (borrowState c)) =
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + ys.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) ∧
    step (program q)
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + ys.length) (r + xs.length) (borrowState (overflow c (xs.zip ys)))) = none := by
  constructor
  · simpa only [hlen] using columns_run c xs ys hlen f g out p s r
  · have hx : putWord f p (xs.map (digitSymbol (q := q))) (p + xs.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf]
    have hy : putWord g s (ys.map (digitSymbol (q := q))) (s + ys.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hg]
    simp [step, program, cfg, hx, hy, readDigit_blank]

/-- The final borrow is represented explicitly in the arithmetic witness;
all source and output cells are specified by the tape postcondition. -/
theorem sub_hoare (xs ys : List (Fin q)) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (s + ys.length) = blank) :
    HoareTime (program q)
      (fun v => v = (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r 0).tapes)
      (fun v => ∃ diff : List (Fin q), ∃ borrow : Bool,
        value xs + q ^ xs.length * bitValue borrow = value ys + value diff ∧
        diff.length = xs.length ∧ v =
          (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
            (putWord out r (diff.map digitSymbol)) (p + xs.length) (s + ys.length) (r + xs.length) 0).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := sub_exact false xs ys hlen f g out p s r hf hg
  refine ⟨_, _, le_rfl, hr, hh, digits false (xs.zip ys), overflow false (xs.zip ys), ?_, ?_, rfl⟩
  · simpa [bitValue] using digits_value false xs ys hlen
  · simp [hlen]

/-- Globally blank-tail output and both complete source words preserved.
Underflow is certified by the final control-state borrow. -/
theorem sub_to_blank (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    let diff := digits false (xs.zip ys)
    let borrow := overflow false (xs.zip ys)
    value xs + q ^ xs.length * bitValue borrow = value ys + value diff ∧
    diff.length = xs.length ∧
    run (program q) xs.length (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol))
      (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol)) (wordTape (diff.map digitSymbol))
        xs.length ys.length xs.length (borrowState borrow)) ∧
    step (program q) (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol)) (wordTape (diff.map digitSymbol))
      xs.length ys.length xs.length (borrowState borrow)) = none := by
  have hw (bits : List (Fin q)) : putWord (fun _ => (blank : Fin (q + 4))) 0 (bits.map digitSymbol) =
      wordTape (bits.map digitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (bits.map digitSymbol)
  obtain ⟨hr, hh⟩ := sub_exact false xs ys hlen (fun _ => (blank : Fin (q + 4)))
    (fun _ => blank) (fun _ => blank) 0 0 0 rfl rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [bitValue] using digits_value false xs ys hlen
  · simp [hlen]
  · simpa only [hw, zero_add, borrowState, Bool.false_eq_true, ↓reduceIte] using hr
  · simpa only [hw, zero_add] using hh

end IntegerMultBounds.Machine.RadixSub
