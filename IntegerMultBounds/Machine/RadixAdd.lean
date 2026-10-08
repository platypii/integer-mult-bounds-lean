import IntegerMultBounds.Machine.RadixDigits
import IntegerMultBounds.Machine.Hoare

/-! Literal fixed-radix modular addition. Three tapes and a two-state carry
perform one transition per input digit. The radix is fixed in the finite
alphabet and transition table; it does not grow with the input width. -/

namespace IntegerMultBounds.Machine.RadixAdd

open RadixDigits
variable {q : ℕ}

def sumDigit (hq : 2 ≤ q) (c : Fin 2) (x y : Fin q) : Fin q :=
  ⟨(x.val + y.val + c.val) % q, Nat.mod_lt _ (by omega)⟩

def carryDigit (hq : 2 ≤ q) (c : Fin 2) (x y : Fin q) : Fin 2 :=
  ⟨(x.val + y.val + c.val) / q, by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have hx := x.isLt
    have hy := y.isLt
    have hc := c.isLt
    omega⟩

theorem full_adder (hq : 2 ≤ q) (c : Fin 2) (x y : Fin q) :
    (sumDigit hq c x y).val + q * (carryDigit hq c x y).val = x.val + y.val + c.val :=
  Nat.mod_add_div _ _

def digits (hq : 2 ≤ q) : Fin 2 → List (Fin q × Fin q) → List (Fin q)
  | _, [] => []
  | c, (x,y) :: rest => sumDigit hq c x y :: digits hq (carryDigit hq c x y) rest

def overflow (hq : 2 ≤ q) : Fin 2 → List (Fin q × Fin q) → Fin 2
  | c, [] => c
  | c, (x,y) :: rest => overflow hq (carryDigit hq c x y) rest

@[simp] theorem digits_length (hq : 2 ≤ q) (c : Fin 2) (cols : List (Fin q × Fin q)) :
    (digits hq c cols).length = cols.length := by
  induction cols generalizing c with
  | nil => rfl
  | cons col rest ih => rcases col with ⟨x,y⟩; simp [digits,ih]

/-- Exact outgoing carry, for arbitrary incoming carry and padded operands. -/
theorem digits_value (hq : 2 ≤ q) (c : Fin 2) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) :
    value (digits hq c (xs.zip ys)) + q ^ xs.length * (overflow hq c (xs.zip ys)).val =
      value xs + value ys + c.val := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [digits,overflow,value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hi := ih (carryDigit hq c x y) ys ht
      have ha := full_adder hq c x y
      simp only [List.zip_cons_cons,digits,overflow,value,List.length_cons,pow_succ]
      nlinarith

theorem digits_value_mod (hq : 2 ≤ q) (c : Fin 2) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) :
    value (digits hq c (xs.zip ys)) = (value xs + value ys + c.val) % q ^ xs.length := by
  rw [← digits_value hq c xs ys hlen,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt _).symm
  have hv := value_lt hq (digits hq c (xs.zip ys))
  simpa [hlen] using hv

/-- The carry is the quotient of the exact sum by the fixed-width modulus. -/
theorem overflow_value (hq : 2 ≤ q) (c : Fin 2) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) :
    (overflow hq c (xs.zip ys)).val = (value xs + value ys + c.val) / q ^ xs.length := by
  have hv : value (digits hq c (xs.zip ys)) < q ^ xs.length := by
    simpa [hlen] using value_lt hq (digits hq c (xs.zip ys))
  rw [← digits_value hq c xs ys hlen,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt hv]
  simp

/-- A finite transition table with digit arithmetic only on scanned symbols. -/
def program (q : ℕ) (hq : 2 ≤ q) : Program 3 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    match readDigit (symbols 0), readDigit (symbols 1) with
    | some x, some y => some (carryDigit hq state x y, fun i =>
        (if i = 2 then digitSymbol (sumDigit hq state x y) else symbols i, .right))
    | _, _ => none

def cfg (f g out : ℤ → Fin (q + 4)) (p s r : ℤ) (state : Fin 2) : Config 3 2 q where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then s else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem digit_step (hq : 2 ≤ q) (c : Fin 2) (x y : Fin q)
    (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hx : f p = digitSymbol x) (hy : g s = digitSymbol y) :
    step (program q hq) (cfg f g out p s r c) =
      some (cfg f g (Function.update out r (digitSymbol (sumDigit hq c x y)))
        (p + 1) (s + 1) (r + 1) (carryDigit hq c x y)) := by
  have ht : (program q hq).transition c
      (fun i => (cfg f g out p s r c).tape i ((cfg f g out p s r c).head i)) =
      some (carryDigit hq c x y, fun i =>
        (if i = 2 then digitSymbol (sumDigit hq c x y)
          else (cfg f g out p s r c).tape i ((cfg f g out p s r c).head i), Move.right)) := by
    simp [program,cfg,hx,hy]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply,eq_comm] <;> intro hj <;> rw [hj]

/-- Exactly one transition per digit; both full source tapes are preserved. -/
theorem columns_run (hq : 2 ≤ q) (c : Fin 2) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) (f g out : ℤ → Fin (q + 4)) (p s r : ℤ) :
    run (program q hq) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r c) =
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits hq c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + xs.length) (r + xs.length) (overflow hq c (xs.zip ys))) := by
  induction xs generalizing ys c f g out p s r with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [run,digits,overflow,putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      have hs := digit_step hq c x y (putWord f p ((x :: xs).map digitSymbol))
        (putWord g s ((y :: ys).map digitSymbol)) out p s r
        (by rw [List.map_cons,putWord_head]) (by rw [List.map_cons,putWord_head])
      simp only [List.length_cons,run,hs,Option.bind_some]
      have hr := ih (carryDigit hq c x y) ys ht (Function.update f p (digitSymbol x))
        (Function.update g s (digitSymbol y)) (Function.update out r (digitSymbol (sumDigit hq c x y)))
        (p + 1) (s + 1) (r + 1)
      simpa only [← putWord_cons,List.map_cons,List.zip_cons_cons,digits,overflow,
        List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hr

/-- Exact-width halting execution, including the outgoing carry in finite control. -/
theorem add_exact (hq : 2 ≤ q) (c : Fin 2) (xs ys : List (Fin q))
    (hlen : xs.length = ys.length) (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hf : f (p + xs.length) = blank) (_hg : g (s + ys.length) = blank) :
    run (program q hq) xs.length
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r c) =
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits hq c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + ys.length) (r + xs.length) (overflow hq c (xs.zip ys))) ∧
    step (program q hq)
      (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
        (putWord out r ((digits hq c (xs.zip ys)).map digitSymbol))
        (p + xs.length) (s + ys.length) (r + xs.length) (overflow hq c (xs.zip ys))) = none := by
  constructor
  · simpa only [hlen] using columns_run hq c xs ys hlen f g out p s r
  · have hx : putWord f p (xs.map digitSymbol) (p + xs.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
    simp [step,program,cfg,hx]

/-- The standard entry state computes modular addition in exactly the source width. -/
theorem add_hoare (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length)
    (f g out : ℤ → Fin (q + 4)) (p s r : ℤ)
    (hf : f (p + xs.length) = blank) (hg : g (s + ys.length) = blank) :
    HoareTime (program q hq)
      (fun v => v = (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol)) out p s r 0).tapes)
      (fun v => ∃ sum : List (Fin q), value sum = (value xs + value ys) % q ^ xs.length ∧
        sum.length = xs.length ∧ v =
          (cfg (putWord f p (xs.map digitSymbol)) (putWord g s (ys.map digitSymbol))
            (putWord out r (sum.map digitSymbol)) (p + xs.length) (s + ys.length) (r + xs.length) 0).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := add_exact hq 0 xs ys hlen f g out p s r hf hg
  refine ⟨_,_,le_rfl,hr,hh,digits hq 0 (xs.zip ys),?_,?_,rfl⟩
  · simpa using digits_value_mod hq 0 xs ys hlen
  · simp [hlen]

/-- Blank-output specialization bundles the numerical result, final carry,
exact runtime, actual halt, and complete preservation of both source tapes. -/
theorem add_to_blank (hq : 2 ≤ q) (xs ys : List (Fin q)) (hlen : xs.length = ys.length) :
    let sum := digits hq 0 (xs.zip ys)
    let carry := overflow hq 0 (xs.zip ys)
    value sum = (value xs + value ys) % q ^ xs.length ∧
    carry.val = (value xs + value ys) / q ^ xs.length ∧
    sum.length = xs.length ∧
    run (program q hq) xs.length
      (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol))
        (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol))
        (wordTape (sum.map digitSymbol)) xs.length ys.length xs.length carry) ∧
    step (program q hq)
      (cfg (wordTape (xs.map digitSymbol)) (wordTape (ys.map digitSymbol))
        (wordTape (sum.map digitSymbol)) xs.length ys.length xs.length carry) = none := by
  have hw (ds : List (Fin q)) : putWord (fun _ => (blank : Fin (q + 4))) 0 (ds.map digitSymbol) =
      wordTape (ds.map digitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (ds.map digitSymbol)
  obtain ⟨hr,hh⟩ := add_exact hq 0 xs ys hlen (fun _ => (blank : Fin (q + 4)))
    (fun _ => blank) (fun _ => blank) 0 0 0 rfl rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa using digits_value_mod hq 0 xs ys hlen
  · simpa using overflow_value hq 0 xs ys hlen
  · simp [hlen]
  · simpa only [hw,zero_add] using hr
  · simpa only [hw,zero_add] using hh

end IntegerMultBounds.Machine.RadixAdd
