import IntegerMultBounds.Machine.BinaryDecrease
import IntegerMultBounds.Machine.PrependRead
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.LoopChain

/-! Literal binary long division on five tapes. The dividend is read from its
most significant bit downwards; each bit is prepended to the remainder,
whose origin moves left one cell per bit, the remainder is compared with the
divisor, and when the divisor fits it is subtracted in place; the quotient
bit is prepended to the quotient word, whose origin also moves left. The
comparison flag lives in one cell that is erased after use. Dividend and
divisor are preserved; the remainder and quotient words are exact, and the
cost is at most `m (4m + 6k + 27)` for an `m`-bit dividend and `k`-bit
divisor. -/

namespace IntegerMultBounds.Machine.BinaryDivide

variable {a : ℕ}

open BinaryCompare (width)
open BinaryDecrease (diffWord diffWord_value diffWord_length)

section Lists

/-- The remainder after one more dividend bit. -/
def stepRem (d r : List Bool) (b : Bool) : List Bool :=
  if Counter.value d ≤ Counter.value (b :: r) then diffWord d (b :: r) else b :: r

/-- The quotient bit for one more dividend bit. -/
def stepQuot (d r : List Bool) (b : Bool) : Bool :=
  decide (Counter.value d ≤ Counter.value (b :: r))

/-- The remainder of the dividend's bits, least significant bit outermost. -/
def remainder (d : List Bool) : List Bool → List Bool
  | [] => []
  | b :: rest => stepRem d (remainder d rest) b

/-- The quotient of the dividend's bits, least significant bit outermost. -/
def quotient (d : List Bool) : List Bool → List Bool
  | [] => []
  | b :: rest => stepQuot d (remainder d rest) b :: quotient d rest

theorem div_correct (d ys : List Bool) (hd : 0 < Counter.value d) :
    Counter.value (remainder d ys) = Counter.value ys % Counter.value d ∧
    Counter.value (quotient d ys) = Counter.value ys / Counter.value d := by
  induction ys with
  | nil => simp [remainder, quotient, Counter.value]
  | cons b rest ih =>
    obtain ⟨hr, hq⟩ := ih
    have hlt : Counter.value (remainder d rest) < Counter.value d := by
      rw [hr]; exact Nat.mod_lt _ hd
    have hsplit := Nat.div_add_mod (Counter.value rest) (Counter.value d)
    rw [← hq, ← hr] at hsplit
    have hval : Counter.value (b :: remainder d rest) =
        (if b then 1 else 0) + 2 * Counter.value (remainder d rest) := by simp [Counter.value]
    have hn : Counter.value (b :: rest) = (if b then 1 else 0) + 2 * Counter.value rest := by
      simp [Counter.value]
    have hB : (if b then 1 else 0) ≤ 1 := by split <;> omega
    by_cases hle : Counter.value d ≤ Counter.value (b :: remainder d rest)
    · have hrem : remainder d (b :: rest) = diffWord d (b :: remainder d rest) := by
        simp [remainder, stepRem, hle]
      have hquot : quotient d (b :: rest) = true :: quotient d rest := by
        simp [quotient, stepQuot, hle]
      rw [hrem, hquot, hn, diffWord_value d _ hle, hval]
      rw [hval] at hle
      simp only [Counter.value, ↓reduceIte]
      have hprod : Counter.value d * (1 + 2 * Counter.value (quotient d rest)) =
          Counter.value d + 2 * (Counter.value d * Counter.value (quotient d rest)) := by ring
      have key := (Nat.div_mod_unique (a := (if b then 1 else 0) + 2 * Counter.value rest)
        (d := 1 + 2 * Counter.value (quotient d rest))
        (c := (if b then 1 else 0) + 2 * Counter.value (remainder d rest) - Counter.value d) hd).mpr
        ⟨by rw [hprod]; omega, by omega⟩
      exact ⟨key.2.symm, key.1.symm⟩
    · have hrem : remainder d (b :: rest) = b :: remainder d rest := by
        simp [remainder, stepRem, hle]
      have hquot : quotient d (b :: rest) = false :: quotient d rest := by
        simp [quotient, stepQuot, hle]
      rw [hrem, hquot, hn, hval]
      rw [hval] at hle
      simp only [Counter.value, Bool.false_eq_true, ↓reduceIte, zero_add]
      have hprod : Counter.value d * (2 * Counter.value (quotient d rest)) =
          2 * (Counter.value d * Counter.value (quotient d rest)) := by ring
      have key := (Nat.div_mod_unique (a := (if b then 1 else 0) + 2 * Counter.value rest)
        (d := 2 * Counter.value (quotient d rest))
        (c := (if b then 1 else 0) + 2 * Counter.value (remainder d rest)) hd).mpr
        ⟨by rw [hprod]; omega, by omega⟩
      exact ⟨key.2.symm, key.1.symm⟩

theorem remainder_length (d ys : List Bool) : (remainder d ys).length ≤ ys.length + d.length := by
  induction ys with
  | nil => simp [remainder]
  | cons b rest ih =>
    simp only [remainder, stepRem]
    split_ifs
    · rw [diffWord_length]
      simp only [width, List.length_cons]
      omega
    · simp only [List.length_cons]; omega

theorem quotient_length (d ys : List Bool) : (quotient d ys).length = ys.length := by
  induction ys with
  | nil => rfl
  | cons b rest ih => simp [quotient, ih]

theorem putWord_getElem (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (k : ℕ)
    (hk : k < xs.length) : putWord f p xs (p + k) = xs[k] := by
  induction xs generalizing f p k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [putWord_head]
    | succ k =>
      rw [putWord_cons, show p + ((k + 1 : ℕ) : ℤ) = p + 1 + k by omega,
        ih _ (p + 1) k (by simpa using hk)]
      rfl

end Lists

section Machine

/-- The five-tape bank: dividend, divisor, remainder, flag, quotient. -/
def bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) : Tapes 5 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩

/-- Dividend and remainder at slots zero and two. -/
def readPlace : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Remainder, divisor and flag at slots two, one and three. -/
def comparePlace : Fin (3 + 2) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 0 else 4
  invFun := fun i => if i = 0 then 3 else if i = 1 then 1 else if i = 2 then 0 else if i = 3 then 2 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at slot three. -/
def flagPlace : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at slot two. -/
def remPlace : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at slot one. -/
def divPlace : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Divisor and remainder at slots one and two. -/
def decreasePlace : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Flag and quotient at slots three and four. -/
def quotPlace : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 0 else if i = 3 then 1 else 2
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def readPart (a : ℕ) : Program 5 4 a :=
  reindex (extend (PrependRead.program (a := a) .left false) 3) readPlace
def comparePart (a : ℕ) : Program 5 4 a := reindex (extend (BinaryCompare.program a) 2) comparePlace
def stepFlag (a : ℕ) : Program 5 2 a := reindex (extend (StepLeft.program (a := a)) 4) flagPlace
def returnRem (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) remPlace
def returnDiv (a : ℕ) : Program 5 3 a := reindex (extend (ReturnOrigin.program (a := a)) 4) divPlace
def decreasePart (a : ℕ) : Program 5 2 a :=
  reindex (extend (BinaryDecrease.program a) 3) decreasePlace
def quotPart (a : ℕ) : Program 5 4 a :=
  reindex (extend (PrependRead.program (a := a) .stay true) 3) quotPlace
def eraseFlag (a : ℕ) : Program 5 2 a := reindex (extend (EraseCell.program (a := a)) 4) flagPlace

def subPart (a : ℕ) : Program 5 8 a := seq (seq (decreasePart a) (returnDiv a)) (returnRem a)

/-- Subtract when the flag says the remainder is not smaller. -/
def cond (a : ℕ) : Program 5 10 a :=
  branch (fun s => decide (s 3 = bitSymbol false)) (subPart a) (skip 5 a (by decide))

/-- Read a bit, compare, return the flag head, rewind remainder and divisor. -/
def prefixPart (a : ℕ) : Program 5 16 a :=
  seq (seq (seq (seq (readPart a) (comparePart a)) (stepFlag a)) (returnRem a)) (returnDiv a)

/-- Write the quotient bit and erase the flag. -/
def suffixPart (a : ℕ) : Program 5 6 a := seq (quotPart a) (eraseFlag a)

def body (a : ℕ) : Program 5 32 a := seq (seq (prefixPart a) (cond a)) (suffixPart a)

def test (s : Fin 5 → Fin (a + 4)) : Bool := decide (s 0 ≠ blank)

/-- The divider: loop over the dividend's bits while its head reads one. -/
def program (a : ℕ) : Program 5 33 a := whileLoop (body a) test

theorem read_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (s : Fin 4) :
    ((PrependRead.cfg f0 f2 p0 p2 s).tapes.append
      (⟨fun i => if i = 0 then p1 else if i = 1 then p3 else p4,
        fun i => if i = 0 then f1 else if i = 1 then f3 else f4⟩ : Tapes 3 a)).reindex readPlace =
      bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append PrependRead.cfg Config.tapes bank readPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem compare_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (s : Fin 4) :
    ((BinaryCompare.cfg f2 f1 f3 p2 p1 p3 s).tapes.append
      (⟨fun i => if i = 0 then p0 else p4, fun i => if i = 0 then f0 else f4⟩ : Tapes 2 a)).reindex
        comparePlace = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append BinaryCompare.cfg Config.tapes bank comparePlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem flag_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p4,
        fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else f4⟩ : Tapes 4 a)).reindex
        flagPlace = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank flagPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem rem_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4,
        fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex
        remPlace = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank remPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem div_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else p4,
        fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex
        divPlace = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append bank divPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem decrease_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (s : Fin 2) :
    ((BinaryDecrease.cfg f1 f2 p1 p2 s).tapes.append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p3 else p4,
        fun i => if i = 0 then f0 else if i = 1 then f3 else f4⟩ : Tapes 3 a)).reindex decreasePlace =
      bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append BinaryDecrease.cfg Config.tapes bank decreasePlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem quot_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (s : Fin 4) :
    ((PrependRead.cfg f3 f4 p3 p4 s).tapes.append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p2,
        fun i => if i = 0 then f0 else if i = 1 then f1 else f2⟩ : Tapes 3 a)).reindex quotPlace =
      bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append PrependRead.cfg Config.tapes bank quotPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem bank_reads (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) (i : Fin 5) :
    (bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4).reads i =
      (bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4).tape i ((bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4).head i) := rfl

variable (ys d : List Bool) (f g : ℤ → Fin (a + 4)) (pn pd pr pf pq : ℤ)

/-- The blank background word placement. -/
abbrev blankWord (p : ℤ) (w : List Bool) : ℤ → Fin (a + 4) :=
  putWord (fun _ => blank) p (w.map bitSymbol)

/-- The bank after the top `i` dividend bits have been consumed. -/
def state (i : ℕ) : Tapes 5 a :=
  bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
    (blankWord (pr - i) (remainder d (ys.drop (ys.length - i)))) (fun _ => blank)
    (blankWord (pq - i) (quotient d (ys.drop (ys.length - i))))
    (pn + ys.length - i - 1) pd (pr - i) pf (pq - i)

/-- The current dividend bit of iteration `i`. -/
def bit (i : ℕ) (hi : i < ys.length) : Bool := ys[ys.length - i - 1]

theorem drop_succ (i : ℕ) (hi : i < ys.length) :
    ys.drop (ys.length - (i + 1)) = bit ys i hi :: ys.drop (ys.length - i) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  congr 2
  omega

theorem state_read (i : ℕ) (hi : i < ys.length) :
    putWord f pn (ys.map bitSymbol) (pn + ys.length - i - 1) = bitSymbol (bit ys i hi) := by
  rw [show pn + (ys.length : ℤ) - i - 1 = pn + ((ys.length - i - 1 : ℕ) : ℤ) by omega,
    putWord_getElem _ _ _ _ (by simp; omega)]
  simp [bit]

/-- Abbreviations for one iteration. -/
local notation "R" i => remainder d (ys.drop (ys.length - i))
local notation "Q" i => quotient d (ys.drop (ys.length - i))

/-- The remainder word after prepending the bit of iteration `i`. -/
def grown (i : ℕ) (hi : i < ys.length) : List Bool := bit ys i hi :: remainder d (ys.drop (ys.length - i))

/-- The comparison flag of iteration `i`. -/
def flag (i : ℕ) (hi : i < ys.length) : Bool :=
  decide (Counter.value (grown ys d i hi) < Counter.value d)

/-- The bank after the compare, flag return and both rewinds of iteration `i`. -/
def compared (i : ℕ) (hi : i < ys.length) : Tapes 5 a :=
  bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
    (blankWord (pr - i - 1) (grown ys d i hi)) (putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)])
    (blankWord (pq - i) (Q i))
    (pn + ys.length - i - 2) pd (pr - i - 1) pf (pq - i)

theorem prefix_steps (hgr : g (pd + d.length) = blank) (hgl : g (pd - 1) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (prefixPart a)
      (fun v => v = state ys d f g pn pd pr pf pq i)
      (fun v => v = compared ys d f g pn pd pr pf pq i hi)
      (2 + 1 + (width (grown ys d i hi) d + 1) + 1 + 1 + 1 + ((grown ys d i hi).length + 2) + 1 +
        (d.length + 2)) := by
  set r := remainder d (ys.drop (ys.length - i)) with hr
  set q := quotient d (ys.drop (ys.length - i)) with hq
  -- read the dividend bit and prepend it to the remainder
  have h1 := hoare_place (PrependRead.prepend_hoare (a := a) .left false (bit ys i hi)
    (putWord f pn (ys.map bitSymbol)) (blankWord (pr - i) r) (pn + ys.length - i - 1) (pr - i)
    (state_read ys f pn i hi)) readPlace
    (⟨fun j => if j = 0 then pd else if j = 1 then pf else pq - i,
      fun j => if j = 0 then putWord g pd (d.map bitSymbol) else if j = 1 then (fun _ => blank)
        else blankWord (pq - i) q⟩ : Tapes 3 a)
  rw [read_bank, read_bank, PrependZero.putWord_prepend_symbol] at h1
  simp only [Bool.xor_false, Move.offset] at h1
  rw [show pn + (ys.length : ℤ) - i - 1 + -1 = pn + ys.length - i - 2 by ring,
    show bitSymbol (bit ys i hi) :: r.map bitSymbol = (grown ys d i hi).map bitSymbol from rfl] at h1
  -- compare the remainder with the divisor
  have h2 := hoare_place (BinaryCompare.compare_hoare (grown ys d i hi) d (fun _ => blank) g
    (fun _ => blank) (pr - i - 1) pd pf rfl hgr) comparePlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol) else blankWord (pq - i) q⟩ : Tapes 2 a)
  rw [compare_bank, compare_bank] at h2
  -- return the flag head
  have h3 := hoare_place (StepLeft.step_hoare (a := a)
    (putWord (fun _ => blank) pf (BinaryCompare.resultWord (grown ys d i hi) d)) (pf + 1)) flagPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pd + d.length
        else if j = 2 then pr - i - 1 + (grown ys d i hi).length else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol) else if j = 1 then putWord g pd (d.map bitSymbol)
        else if j = 2 then blankWord (pr - i - 1) (grown ys d i hi) else blankWord (pq - i) q⟩ : Tapes 4 a)
  simp only [StepLeft.cfg, Config.tapes] at h3
  rw [flag_bank, flag_bank, add_sub_cancel_right] at h3
  -- rewind the remainder
  have h4 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) (pr - i - 1)
    ((grown ys d i hi).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) remPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pd + d.length
        else if j = 2 then pf else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol) else if j = 1 then putWord g pd (d.map bitSymbol)
        else if j = 2 then putWord (fun _ => blank) pf (BinaryCompare.resultWord (grown ys d i hi) d)
        else blankWord (pq - i) q⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h4
  rw [rem_bank, rem_bank, List.length_map] at h4
  -- rewind the divisor
  have h5 := hoare_place (ReturnOrigin.return_hoare_at g pd (d.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hgl) divPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pr - i - 1
        else if j = 2 then pf else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol)
        else if j = 1 then blankWord (pr - i - 1) (grown ys d i hi)
        else if j = 2 then putWord (fun _ => blank) pf (BinaryCompare.resultWord (grown ys d i hi) d)
        else blankWord (pq - i) q⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h5
  rw [div_bank, div_bank, List.length_map] at h5
  have hpre : state ys d f g pn pd pr pf pq i =
      bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol)) (blankWord (pr - i) r)
        (fun _ => blank) (blankWord (pq - i) q) (pn + ys.length - i - 1) pd (pr - i) pf (pq - i) := rfl
  have hpost : compared ys d f g pn pd pr pf pq i hi =
      bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
        (blankWord (pr - i - 1) (grown ys d i hi))
        (putWord (fun _ => blank) pf (BinaryCompare.resultWord (grown ys d i hi) d))
        (blankWord (pq - i) q) (pn + ys.length - i - 2) pd (pr - i - 1) pf (pq - i) := rfl
  rw [hpre, hpost]
  exact (((h1.seq h2).seq h3).seq h4).seq h5

/-- The bank after the conditional subtraction of iteration `i`. -/
def subtracted (i : ℕ) (hi : i < ys.length) : Tapes 5 a :=
  bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
    (blankWord (pr - i - 1) (stepRem d (R i) (bit ys i hi)))
    (putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)])
    (blankWord (pq - i) (Q i))
    (pn + ys.length - i - 2) pd (pr - i - 1) pf (pq - i)

/-- The cost of the subtraction branch at iteration `i`. -/
def subCost (i : ℕ) (hi : i < ys.length) : ℕ :=
  width (grown ys d i hi) d + 1 + (d.length + 2) + 1 + (width (grown ys d i hi) d + 2)

theorem sub_step (hgr : g (pd + d.length) = blank) (hgl : g (pd - 1) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (subPart a) (fun v => v = compared ys d f g pn pd pr pf pq i hi)
      (fun v => v = bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
        (blankWord (pr - i - 1) (diffWord d (grown ys d i hi)))
        (putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)])
        (blankWord (pq - i) (Q i))
        (pn + ys.length - i - 2) pd (pr - i - 1) pf (pq - i))
      (subCost ys d i hi) := by
  have h1 := hoare_place (BinaryDecrease.decrease_hoare d (grown ys d i hi) g (fun _ => blank) pd
    (pr - i - 1) hgr (fun _ _ _ => rfl)) decreasePlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pf else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol)
        else if j = 1 then putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)]
        else blankWord (pq - i) (Q i)⟩ : Tapes 3 a)
  rw [decrease_bank, decrease_bank] at h1
  have h2 := hoare_place (ReturnOrigin.return_hoare_at g pd (d.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hgl) divPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2
        else if j = 1 then pr - i - 1 + width (grown ys d i hi) d else if j = 2 then pf else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol)
        else if j = 1 then blankWord (pr - i - 1) (diffWord d (grown ys d i hi))
        else if j = 2 then putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)]
        else blankWord (pq - i) (Q i)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h2
  rw [div_bank, div_bank, List.length_map] at h2
  have h3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) (pr - i - 1)
    ((diffWord d (grown ys d i hi)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) remPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pd
        else if j = 2 then pf else pq - i,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol) else if j = 1 then putWord g pd (d.map bitSymbol)
        else if j = 2 then putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)]
        else blankWord (pq - i) (Q i)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h3
  rw [rem_bank, rem_bank, List.length_map, diffWord_length] at h3
  exact (h1.seq h2).seq h3

theorem compared_reads (i : ℕ) (hi : i < ys.length) :
    (compared ys d f g pn pd pr pf pq i hi).reads 3 = bitSymbol (flag ys d i hi) := by
  simp [compared, Tapes.reads, bank, putWord]

theorem cond_step (hgr : g (pd + d.length) = blank) (hgl : g (pd - 1) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (cond a) (fun v => v = compared ys d f g pn pd pr pf pq i hi)
      (fun v => v = subtracted ys d f g pn pd pr pf pq i hi) (max (subCost ys d i hi) 0 + 1) := by
  unfold cond
  have hread : decide ((compared ys d f g pn pd pr pf pq i hi).reads 3 = bitSymbol false) =
      !flag ys d i hi := by
    rw [compared_reads]
    cases flag ys d i hi <;> simp [bitSymbol]
  cases hb : flag ys d i hi
  · -- the remainder is not smaller: subtract
    refine branch_hoare _ ((sub_step ys d f g pn pd pr pf pq hgr hgl i hi).consequence
      (fun v hv => hv.1) (fun v hv => ?_) le_rfl) (fun v ⟨hv, hv'⟩ => ?_)
    · rw [hv, subtracted, stepRem]
      have hle : Counter.value d ≤ Counter.value (grown ys d i hi) := by
        simp only [flag, decide_eq_false_iff_not, not_lt] at hb; exact hb
      simp only [grown] at hle
      simp only [hle, ↓reduceIte]
      rfl
    · exfalso; rw [hv, hread, hb] at hv'; simp at hv'
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) ((skip_hoare _ _).consequence
      (fun v hv => hv.1) (fun v hv => ?_) le_rfl)
    · exfalso; rw [hv, hread, hb] at hv'; simp at hv'
    · rw [hv, subtracted, compared, stepRem]
      have hlt : Counter.value (grown ys d i hi) < Counter.value d := by
        simpa [flag] using hb
      simp only [grown] at hlt
      simp only [not_le.mpr hlt, ↓reduceIte]
      rfl

theorem flag_not (i : ℕ) (hi : i < ys.length) :
    (!flag ys d i hi) = stepQuot d (R i) (bit ys i hi) := by
  unfold flag stepQuot grown
  rw [← decide_not]
  exact decide_eq_decide.mpr not_lt

theorem suffix_steps (i : ℕ) (hi : i < ys.length) :
    HoareTime (suffixPart a)
      (fun v => v = subtracted ys d f g pn pd pr pf pq i hi)
      (fun v => v = state ys d f g pn pd pr pf pq (i + 1)) (2 + 1 + 1) := by
  have h1 := hoare_place (PrependRead.prepend_hoare (a := a) .stay true (flag ys d i hi)
    (putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)]) (blankWord (pq - i) (Q i)) pf (pq - i)
    (by simp [putWord])) quotPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pd else pr - i - 1,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol)
        else if j = 1 then putWord g pd (d.map bitSymbol)
        else blankWord (pr - i - 1) (stepRem d (R i) (bit ys i hi))⟩ : Tapes 3 a)
  rw [quot_bank, quot_bank, PrependZero.putWord_prepend_symbol] at h1
  simp only [Bool.xor_true, Move.offset, add_zero, flag_not] at h1
  have h2 := hoare_place (EraseCell.erase_hoare (a := a)
    (putWord (fun _ => blank) pf [bitSymbol (flag ys d i hi)]) pf) flagPlace
    (⟨fun j => if j = 0 then pn + ys.length - i - 2 else if j = 1 then pd
        else if j = 2 then pr - i - 1 else pq - i - 1,
      fun j => if j = 0 then putWord f pn (ys.map bitSymbol)
        else if j = 1 then putWord g pd (d.map bitSymbol)
        else if j = 2 then blankWord (pr - i - 1) (stepRem d (R i) (bit ys i hi))
        else blankWord (pq - i - 1) (stepQuot d (R i) (bit ys i hi) :: Q i)⟩ : Tapes 4 a)
  simp only [EraseCell.cfg, Config.tapes] at h2
  rw [flag_bank, flag_bank, EraseCell.erase_single] at h2
  refine (h1.seq h2).consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
  rw [hv, state, drop_succ ys i hi, remainder, quotient]
  congr 1 <;> push_cast <;> ring_nf

/-- The exact body cost at iteration `i`. -/
def iterCost (i : ℕ) (hi : i < ys.length) : ℕ :=
  (2 + 1 + (width (grown ys d i hi) d + 1) + 1 + 1 + 1 + ((grown ys d i hi).length + 2) + 1 +
    (d.length + 2)) + 1 + (max (subCost ys d i hi) 0 + 1) + 1 + (2 + 1 + 1)

theorem body_step (hgr : g (pd + d.length) = blank) (hgl : g (pd - 1) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (body a) (fun v => v = state ys d f g pn pd pr pf pq i)
      (fun v => v = state ys d f g pn pd pr pf pq (i + 1)) (iterCost ys d i hi) := by
  have h := ((prefix_steps ys d f g pn pd pr pf pq hgr hgl i hi).seq
    (cond_step ys d f g pn pd pr pf pq hgr hgl i hi)).seq (suffix_steps ys d f g pn pd pr pf pq i hi)
  exact h

/-- A total cost function over all indices. -/
def costAt (i : ℕ) : ℕ := if hi : i < ys.length then iterCost ys d i hi else 0

theorem state_reads (i : ℕ) (hi : i < ys.length) :
    test (state ys d f g pn pd pr pf pq i).reads = true := by
  simp only [test, state, Tapes.reads, bank, ↓reduceIte]
  rw [state_read ys f pn i hi]
  cases bit ys i hi <;> simp [bitSymbol, blank]

theorem state_exit (hfl : f (pn - 1) = blank) :
    test (state ys d f g pn pd pr pf pq ys.length).reads = false := by
  simp only [test, state, Tapes.reads, bank, ↓reduceIte]
  rw [putWord_outside _ _ _ _ (Or.inl (by omega)),
    show pn + (ys.length : ℤ) - ys.length - 1 = pn - 1 by ring, hfl]
  simp

theorem loop_hoare (hfl : f (pn - 1) = blank) (hgr : g (pd + d.length) = blank)
    (hgl : g (pd - 1) = blank) :
    HoareTime (program a) (fun v => v = state ys d f g pn pd pr pf pq 0)
      (fun v => v = state ys d f g pn pd pr pf pq ys.length)
      (∑ i ∈ Finset.range ys.length, (costAt ys d i + 2)) :=
  while_chain_hoare (body a) test (state ys d f g pn pd pr pf pq) (costAt ys d) ys.length
    (fun i hi => by
      have h := body_step ys d f g pn pd pr pf pq hgr hgl i hi
      simpa [costAt, hi] using h)
    (fun i hi => state_reads ys d f g pn pd pr pf pq i hi)
    (state_exit ys d f g pn pd pr pf pq hfl)

theorem state_zero : state ys d f g pn pd pr pf pq 0 =
    bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol)) (fun _ => blank)
      (fun _ => blank) (fun _ => blank) (pn + ys.length - 1) pd pr pf pq := by
  simp [state, remainder, quotient, blankWord, putWord]

theorem state_final : state ys d f g pn pd pr pf pq ys.length =
    bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
      (blankWord (pr - ys.length) (remainder d ys)) (fun _ => blank)
      (blankWord (pq - ys.length) (quotient d ys))
      (pn - 1) pd (pr - ys.length) pf (pq - ys.length) := by
  simp [state]

/-- The division contract in terms of the input words: the remainder and
quotient words sit at the shifted origins, dividend and divisor are
preserved, and the flag tape is blank again. -/
theorem divide_hoare (hfl : f (pn - 1) = blank) (hgr : g (pd + d.length) = blank)
    (hgl : g (pd - 1) = blank) :
    HoareTime (program a)
      (fun v => v = bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
        (fun _ => blank) (fun _ => blank) (fun _ => blank) (pn + ys.length - 1) pd pr pf pq)
      (fun v => v = bank (putWord f pn (ys.map bitSymbol)) (putWord g pd (d.map bitSymbol))
        (blankWord (pr - ys.length) (remainder d ys)) (fun _ => blank)
        (blankWord (pq - ys.length) (quotient d ys))
        (pn - 1) pd (pr - ys.length) pf (pq - ys.length))
      (∑ i ∈ Finset.range ys.length, (costAt ys d i + 2)) := by
  have h := loop_hoare ys d f g pn pd pr pf pq hfl hgr hgl
  rw [state_zero, state_final] at h
  exact h

end Machine

section Cost

variable (ys d : List Bool)

theorem grown_length_le (i : ℕ) (hi : i < ys.length) :
    (grown ys d i hi).length ≤ ys.length + d.length := by
  have := remainder_length d (ys.drop (ys.length - i))
  have hd : (ys.drop (ys.length - i)).length = i := by simp; omega
  simp only [grown, List.length_cons]
  omega

theorem width_le (i : ℕ) (hi : i < ys.length) :
    width (grown ys d i hi) d ≤ ys.length + d.length := by
  have := grown_length_le ys d i hi
  simp only [width]
  omega

theorem iterCost_le (i : ℕ) (hi : i < ys.length) :
    iterCost ys d i hi + 2 ≤ 4 * ys.length + 6 * d.length + 27 := by
  have h1 := grown_length_le ys d i hi
  have h2 := width_le ys d i hi
  unfold iterCost subCost
  omega

theorem costAt_le (i : ℕ) : costAt ys d i + 2 ≤ 4 * ys.length + 6 * d.length + 27 := by
  unfold costAt
  split_ifs with hi
  · exact iterCost_le ys d i hi
  · omega

/-- The total cost is at most `m (4m + 6k + 27)`. -/
theorem cost_le :
    ∑ i ∈ Finset.range ys.length, (costAt ys d i + 2) ≤
      ys.length * (4 * ys.length + 6 * d.length + 27) := by
  calc ∑ i ∈ Finset.range ys.length, (costAt ys d i + 2)
      ≤ ∑ _i ∈ Finset.range ys.length, (4 * ys.length + 6 * d.length + 27) :=
        Finset.sum_le_sum fun i _ => costAt_le ys d i
    _ = ys.length * (4 * ys.length + 6 * d.length + 27) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Cost

end IntegerMultBounds.Machine.BinaryDivide
