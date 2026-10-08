import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.BinaryAccumulate
import IntegerMultBounds.Machine.BinaryDecrease
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.WordMoves
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.LoopChain

/-! Ordered selection of records by a modular counter. A list of nonblank
records separated by single blanks is scanned once; before each record a
constant is added to a counter word, and the record is copied to the output
exactly when the counter reaches a second constant, which is then subtracted.
With the constants `2s`, `2t` and the initial counter `2t - s - 1` this is the
row-selecting map `C` of the resampling interface: it copies the records at
the indices `[tj/s]`, `0 ≤ j < s`, in order, in one pass of linear cost
(the value semantics are proved here, the index identity in `RowSelect`).
Six tapes: input, output, counter, addend, modulus, comparison flag. -/

namespace IntegerMultBounds.Machine.OrderedSelect

open BinaryAccumulate (sumWord)
open BinaryDecrease (diffWord)
open Counter (value)

variable {a : ℕ}

/-- The six-tape bank: input, output, counter, addend, modulus, flag. -/
def bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) : Tapes 6 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else p5,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3
    else if i = 4 then f4 else f5⟩

def E3_2 : Fin (2 + 4) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 0 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E3_2_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun i => if i = 0 then p3 else p2, fun i => if i = 0 then f3 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p4 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f4 else f5⟩ : Tapes 4 a)).reindex E3_2 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E3_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E3 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E3_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p4 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f4 else f5⟩ : Tapes 5 a)).reindex E3 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else if i = 3 then p4 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else if i = 3 then f4 else f5⟩ : Tapes 5 a)).reindex E2 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2_4_5 : Fin (3 + 3) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 0 else if i = 4 then 1 else 3
  invFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 0 else if i = 3 then 5 else if i = 4 then 1 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_4_5_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun i => if i = 0 then p2 else if i = 1 then p4 else p5, fun i => if i = 0 then f2 else if i = 1 then f4 else f5⟩ : Tapes 3 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p3, fun i => if i = 0 then f0 else if i = 1 then f1 else f3⟩ : Tapes 3 a)).reindex E2_4_5 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E2_4_5
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E4 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 0 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p4, fun _ => f4⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f5⟩ : Tapes 5 a)).reindex E4 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E5 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E5_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p5, fun _ => f5⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩ : Tapes 5 a)).reindex E5 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E5
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4 else p5, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else if i = 3 then f4 else f5⟩ : Tapes 5 a)).reindex E0 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E4_2 : Fin (2 + 4) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 3 else 5
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 0 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_2_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun i => if i = 0 then p4 else p2, fun i => if i = 0 then f4 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f5⟩ : Tapes 4 a)).reindex E4_2 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E4_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0_1 : Fin (2 + 4) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p2 else if i = 1 then p3 else if i = 2 then p4 else p5, fun i => if i = 0 then f2 else if i = 1 then f3 else if i = 2 then f4 else f5⟩ : Tapes 4 a)).reindex E0_1 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E0_1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 5) ≃ Fin 6 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else 5
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 f2 f3 f4 f5 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4 else p5, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else if i = 3 then f4 else f5⟩ : Tapes 5 a)).reindex E1 = bank f0 f1 f2 f3 f4 f5 p0 p1 p2 p3 p4 p5 := by
  unfold Tapes.reindex Tapes.append bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

section Parts

def acc : Program 6 3 a := reindex (extend (BinaryAccumulate.program a) 4) E3_2
def retS : Program 6 3 a := reindex (extend (ReturnOrigin.program (a := a)) 5) E3
def retR : Program 6 3 a := reindex (extend (ReturnOrigin.program (a := a)) 5) E2
def cmp : Program 6 4 a := reindex (extend (BinaryCompare.program a) 3) E2_4_5
def retT : Program 6 3 a := reindex (extend (ReturnOrigin.program (a := a)) 5) E4
def leftF : Program 6 2 a := reindex (extend (StepLeft.program (a := a)) 5) E5
def scanI : Program 6 1 a := reindex (extend (ScanEnd.program (a := a)) 5) E0
def rightI : Program 6 2 a := reindex (extend (StepRight.program (a := a)) 5) E0
def dec : Program 6 2 a := reindex (extend (BinaryDecrease.program a) 4) E4_2
def copyIO : Program 6 1 a := reindex (extend (CopyWord.program (a := a)) 4) E0_1
def rightO : Program 6 2 a := reindex (extend (StepRight.program (a := a)) 5) E1
def eraseF : Program 6 2 a := reindex (extend (EraseCell.program (a := a)) 5) E5

/-- Add the addend to the counter, compare with the modulus, park every head. -/
def prefixPart :=
  seq (seq (seq (seq (seq (seq (acc (a := a)) retS) retR) cmp) retR) retT) leftF
/-- Below the modulus: skip the record. -/
def skipChain := seq (seq (scanI (a := a)) rightI) eraseF
/-- At or above the modulus: subtract it and copy the record. -/
def copyChain := seq (seq (seq (seq (seq (seq (dec (a := a)) retT) retR) copyIO) rightI) rightO) eraseF
def condPart := branch (fun sy => decide (sy 5 = bitSymbol true)) (skipChain (a := a)) copyChain
/-- One record. -/
def body := seq (prefixPart (a := a)) condPart
/-- Continue while the input head reads a record. -/
def test : (Fin 6 → Fin (a + 4)) → Bool := fun sy => decide (sy 0 ≠ blank)
/-- The selection machine. -/
def program := whileLoop (body (a := a)) test

end Parts

section Words

/-- The counter after `i` records: add the addend, subtract the modulus when reached. -/
def rWord (S T R0 : List Bool) : ℕ → List Bool
  | 0 => R0
  | i + 1 =>
    if value T ≤ value (sumWord S (rWord S T R0 i)) then diffWord T (sumWord S (rWord S T R0 i))
    else sumWord S (rWord S T R0 i)

/-- Whether record `i` is selected: the comparison flag is not "less". -/
def sel (S T R0 : List Bool) (i : ℕ) : Bool :=
  !decide (value (sumWord S (rWord S T R0 i)) < value T)

theorem rWord_succ (S T R0 : List Bool) (i : ℕ) :
    rWord S T R0 (i + 1) =
      if sel S T R0 i then diffWord T (sumWord S (rWord S T R0 i)) else sumWord S (rWord S T R0 i) := by
  simp only [rWord, sel, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]

/-- The selected records among the first `i`. -/
def selected (recs : List (List (Fin (a + 4)))) (S T R0 : List Bool) : ℕ → List (List (Fin (a + 4)))
  | 0 => []
  | i + 1 => selected recs S T R0 i ++ (if sel S T R0 i then [recs.getD i []] else [])

/-- Records separated by single blanks. -/
def flat (recs : List (List (Fin (a + 4)))) : List (Fin (a + 4)) := (recs.map (· ++ [blank])).flatten

/-- The origin of record `i`. -/
def start (recs : List (List (Fin (a + 4)))) (i : ℕ) : ℕ := (flat (recs.take i)).length

/-- The input tape. -/
def inTape (recs : List (List (Fin (a + 4)))) : ℤ → Fin (a + 4) := putWord (fun _ => blank) 0 (flat recs)

/-- The input tape without record `i`. -/
def bg (recs : List (List (Fin (a + 4)))) (i : ℕ) : ℤ → Fin (a + 4) :=
  putWord (putWord (fun _ => blank) 0 (flat (recs.take i)))
    ((start recs i : ℤ) + (recs.getD i []).length) (blank :: flat (recs.drop (i + 1)))

theorem flat_append (xs ys : List (List (Fin (a + 4)))) : flat (xs ++ ys) = flat xs ++ flat ys := by
  simp [flat]

theorem flat_cons (r : List (Fin (a + 4))) (rs : List (List (Fin (a + 4)))) :
    flat (r :: rs) = r ++ (blank :: flat rs) := by
  simp [flat]

theorem flat_nil : flat ([] : List (List (Fin (a + 4)))) = [] := rfl

theorem flat_singleton (r : List (Fin (a + 4))) : flat [r] = r ++ [blank] := by simp [flat]

theorem getD_eq (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length) :
    recs.getD i [] = recs[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem take_succ_getD (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length) :
    recs.take (i + 1) = recs.take i ++ [recs.getD i []] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, getD_eq _ _ hi]
  rfl

theorem start_succ (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length) :
    start recs (i + 1) = start recs i + (recs.getD i []).length + 1 := by
  simp only [start, take_succ_getD recs i hi, flat_append, flat_singleton, List.length_append,
    List.length_singleton]
  omega

theorem start_zero (recs : List (List (Fin (a + 4)))) : start recs 0 = 0 := rfl

theorem start_length (recs : List (List (Fin (a + 4)))) : start recs recs.length = (flat recs).length := by
  simp [start]

/-- The input tape is record `i` over its background. -/
theorem inTape_repr (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length) :
    inTape recs = putWord (bg recs i) (start recs i) (recs.getD i []) := by
  have hsplit : flat recs = flat (recs.take i) ++ (recs.getD i [] ++ (blank :: flat (recs.drop (i + 1)))) := by
    conv_lhs => rw [← List.take_append_drop i recs]
    rw [flat_append, List.drop_eq_getElem_cons hi, flat_cons, getD_eq _ _ hi]
  rw [inTape, hsplit, ← putWord_append_forward, putWord_append, bg, start]
  simp

theorem bg_blank (recs : List (List (Fin (a + 4)))) (i : ℕ) :
    bg recs i ((start recs i : ℤ) + (recs.getD i []).length) = blank := putWord_head _ _ _ _

/-- Beyond the last record the input is blank. -/
theorem inTape_end (recs : List (List (Fin (a + 4)))) : inTape recs (start recs recs.length) = blank := by
  rw [start_length, inTape, putWord_outside _ _ _ _ (Or.inr (by simp))]

/-- At a record origin the input reads its first symbol, which is not blank. -/
theorem inTape_start (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length)
    (hne : recs.getD i [] ≠ []) (hnb : ∀ x ∈ recs.getD i [], x ≠ blank) :
    inTape recs (start recs i) ≠ blank := by
  rw [inTape_repr recs i hi]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  rw [hx, putWord_head]
  exact hnb x (by rw [hx]; exact List.mem_cons_self)

/-- Writing a blank after a word on a blank background changes nothing. -/
theorem putWord_blank_snoc (p : ℤ) (xs : List (Fin (a + 4))) :
    putWord (fun _ => blank) p (xs ++ [blank]) = putWord (fun _ => blank) p xs := by
  rw [← putWord_append_forward]
  simp only [putWord]
  rw [Function.update_eq_self_iff, putWord_outside _ _ _ _ (Or.inr le_rfl)]

end Words

section Bounds

/-- Cost bounds in terms of the counter widths and the record length. -/
def prefix_hoareBound (twoS twoT R0 : List Bool) (i : ℕ) : ℕ :=
  (BinaryAccumulate.width twoS (rWord twoS twoT R0 i) + 1) + 1 + (twoS.length + 2) + 1 +
  ((sumWord twoS (rWord twoS twoT R0 i)).length + 2) + 1 +
  (BinaryCompare.width (sumWord twoS (rWord twoS twoT R0 i)) twoT + 1) + 1 +
  ((sumWord twoS (rWord twoS twoT R0 i)).length + 2) + 1 + (twoT.length + 2) + 1 + 1
def skip_hoareBound (r : ℕ) : ℕ := r + 1 + 1 + 1 + 1
def copy_hoareBound (twoS twoT R0 : List Bool) (r i : ℕ) : ℕ :=
  BinaryCompare.width (sumWord twoS (rWord twoS twoT R0 i)) twoT + 1 + (twoT.length + 2) + 1 +
  (BinaryCompare.width (sumWord twoS (rWord twoS twoT R0 i)) twoT + 2) + 1 + r + 1 + 1 + 1 + 1 + 1 + 1

end Bounds

theorem prefix_hoare (recs : List (List (Fin (a + 4)))) (twoS twoT R0 : List Bool) (pO pR pS pT pF : ℤ) (i : ℕ) :
    ∃ c, HoareTime (prefixPart) (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((rWord twoS twoT R0 i).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) ((fun _ => blank)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF))
      (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)) c ∧ c ≤ prefix_hoareBound twoS twoT R0 i := by
  have s1 := hoare_place (BinaryAccumulate.accumulate_hoare twoS (rWord twoS twoT R0 i) (fun _ => blank) (fun _ => blank) pS pR rfl (fun _ _ _ => rfl)) E3_2
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pT else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [BinaryAccumulate.cfg, Config.tapes] at s1
  rw [E3_2_bank, E3_2_bank] at s1
  have s2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pS (twoS.map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pR + ↑(sumWord twoS (rWord twoS twoT R0 i)).length else if j = 3 then pT else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else (fun _ => blank)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s2
  rw [E3_bank, E3_bank, List.length_map] at s2
  have s3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else (fun _ => blank)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s3
  rw [E2_bank, E2_bank, List.length_map] at s3
  have s4 := hoare_place (BinaryCompare.compare_hoare (sumWord twoS (rWord twoS twoT R0 i)) twoT (fun _ => blank) (fun _ => blank) (fun _ => blank) pR pT pF rfl rfl) E2_4_5
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else pS, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else putWord (fun _ => blank) pS ((twoS).map bitSymbol)⟩ : Tapes 3 a)
  simp only [BinaryCompare.cfg, Config.tapes] at s4
  rw [E2_4_5_bank, E2_4_5_bank] at s4
  have s5 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pS else if j = 3 then pT + ↑twoT.length else pF + 1, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s5
  rw [E2_bank, E2_bank, List.length_map] at s5
  have s6 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pT (twoT.map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E4
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pR else if j = 3 then pS else pF + 1, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s6
  rw [E4_bank, E4_bank, List.length_map] at s6
  have s7 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) (pF + 1)) E5
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pR else if j = 3 then pS else pT, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pT ((twoT).map bitSymbol)⟩ : Tapes 5 a)
  simp only [StepLeft.cfg, Config.tapes] at s7
  rw [E5_bank, E5_bank, add_sub_cancel_right] at s7
  refine ⟨_, ((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7), ?_⟩
  unfold prefix_hoareBound
  omega

theorem skip_hoare (recs : List (List (Fin (a + 4)))) (twoS twoT R0 : List Bool) (pO pR pS pT pF : ℤ) (i : ℕ)
    (hi : i < recs.length) (hnb : ∀ x ∈ recs.getD i [], x ≠ blank) :
    ∃ c, HoareTime (skipChain) (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF))
      (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) ((fun _ => blank)) ((start recs (i + 1) : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)) c ∧ c ≤ skip_hoareBound (recs.getD i []).length := by
  have hrepr := inTape_repr recs i hi
  have hstart : (start recs i : ℤ) + ↑(recs.getD i []).length + 1 = ↑(start recs (i + 1)) := by
    rw [start_succ recs i hi]; push_cast; ring
  have k1 := hoare_place (ScanEnd.scan_hoare (bg recs i) (start recs i : ℤ) (recs.getD i []) hnb (bg_blank recs i)) E0
    (⟨fun j => if j = 0 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 1 then pR else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 1 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [ScanEnd.cfg, Config.tapes] at k1
  rw [E0_bank, E0_bank, ← hrepr] at k1
  have k2 := hoare_place (StepRight.step_hoare (inTape recs) ((start recs i : ℤ) + ↑(recs.getD i []).length)) E0
    (⟨fun j => if j = 0 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 1 then pR else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 1 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [StepRight.cfg, Config.tapes] at k2
  rw [E0_bank, E0_bank, hstart] at k2
  have k3 := hoare_place (EraseCell.erase_hoare (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) pF) E5
    (⟨fun j => if j = 0 then (start recs (i + 1) : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pR else if j = 3 then pS else pT, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pT ((twoT).map bitSymbol)⟩ : Tapes 5 a)
  simp only [EraseCell.cfg, Config.tapes] at k3
  rw [E5_bank, E5_bank, BinaryCompare.resultWord, EraseCell.erase_single] at k3
  refine ⟨_, ((k1.seq k2).seq k3), ?_⟩
  unfold skip_hoareBound
  omega

theorem copy_hoare (recs : List (List (Fin (a + 4)))) (twoS twoT R0 : List Bool) (pO pR pS pT pF : ℤ) (i : ℕ)
    (hi : i < recs.length) (hnb : ∀ x ∈ recs.getD i [], x ≠ blank) :
    ∃ c, HoareTime (copyChain) (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF))
      (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i) ++ recs.getD i [])) (putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) ((fun _ => blank)) ((start recs (i + 1) : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length + ↑(recs.getD i []).length + 1) (pR) (pS) (pT) (pF)) c ∧ c ≤ copy_hoareBound twoS twoT R0 (recs.getD i []).length i := by
  have hrepr := inTape_repr recs i hi
  have hstart : (start recs i : ℤ) + ↑(recs.getD i []).length + 1 = ↑(start recs (i + 1)) := by
    rw [start_succ recs i hi]; push_cast; ring
  have c1 := hoare_place (BinaryDecrease.decrease_hoare twoT (sumWord twoS (rWord twoS twoT R0 i)) (fun _ => blank) (fun _ => blank) pT pR rfl (fun _ _ _ => rfl)) E4_2
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pS else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 4 a)
  simp only [BinaryDecrease.cfg, Config.tapes] at c1
  rw [E4_2_bank, E4_2_bank] at c1
  have c2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pT (twoT.map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E4
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pR + ↑(BinaryCompare.width (sumWord twoS (rWord twoS twoT R0 i)) twoT) else if j = 3 then pS else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c2
  rw [E4_bank, E4_bank, List.length_map] at c2
  have c3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then (start recs i : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c3
  rw [E2_bank, E2_bank, List.length_map, BinaryDecrease.diffWord_length] at c3
  have c4 := hoare_place (CopyWord.copy_hoare (bg recs i) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (start recs i : ℤ) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (recs.getD i []) hnb (bg_blank recs i)) E0_1
    (⟨fun j => if j = 0 then pR else if j = 1 then pS else if j = 2 then pT else pF, fun j => if j = 0 then putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) else if j = 1 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 4 a)
  simp only [CopyWord.cfg, Config.tapes] at c4
  rw [E0_1_bank, E0_1_bank, ← hrepr, putWord_append_forward] at c4
  have c5 := hoare_place (StepRight.step_hoare (inTape recs) ((start recs i : ℤ) + ↑(recs.getD i []).length)) E0
    (⟨fun j => if j = 0 then pO + ↑(flat (selected recs twoS twoT R0 i)).length + ↑(recs.getD i []).length else if j = 1 then pR else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i) ++ recs.getD i []) else if j = 1 then putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [StepRight.cfg, Config.tapes] at c5
  rw [E0_bank, E0_bank, hstart] at c5
  have c6 := hoare_place (StepRight.step_hoare (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i) ++ recs.getD i [])) (pO + ↑(flat (selected recs twoS twoT R0 i)).length + ↑(recs.getD i []).length)) E1
    (⟨fun j => if j = 0 then (start recs (i + 1) : ℤ) else if j = 1 then pR else if j = 2 then pS else if j = 3 then pT else pF, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pT ((twoT).map bitSymbol) else putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)⟩ : Tapes 5 a)
  simp only [StepRight.cfg, Config.tapes] at c6
  rw [E1_bank, E1_bank] at c6
  have c7 := hoare_place (EraseCell.erase_hoare (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) pF) E5
    (⟨fun j => if j = 0 then (start recs (i + 1) : ℤ) else if j = 1 then pO + ↑(flat (selected recs twoS twoT R0 i)).length + ↑(recs.getD i []).length + 1 else if j = 2 then pR else if j = 3 then pS else pT, fun j => if j = 0 then inTape recs else if j = 1 then putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i) ++ recs.getD i []) else if j = 2 then putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pS ((twoS).map bitSymbol) else putWord (fun _ => blank) pT ((twoT).map bitSymbol)⟩ : Tapes 5 a)
  simp only [EraseCell.cfg, Config.tapes] at c7
  rw [E5_bank, E5_bank, BinaryCompare.resultWord, EraseCell.erase_single] at c7
  refine ⟨_, ((((((c1.seq c2).seq c3).seq c4).seq c5).seq c6).seq c7), ?_⟩
  unfold copy_hoareBound
  omega

section Invariant

theorem value_append_true (xs : List Bool) : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih => cases b <;> simp [value, ih, pow_succ] <;> omega

/-- Without overflow the sum word has the common width. -/
theorem sumWord_length_of_lt (xs acc : List Bool)
    (h : value xs + value acc < 2 ^ BinaryAccumulate.width xs acc) :
    (sumWord xs acc).length = BinaryAccumulate.width xs acc := by
  rw [BinaryAccumulate.sumWord_length]
  cases hov : BinaryAdd.overflow false (BinaryAccumulate.pairs xs acc)
  · simp [BinaryAdd.carryWord]
  · exfalso
    have hv := BinaryAccumulate.sumWord_value xs acc
    have hs : sumWord xs acc = BinaryAdd.digits false (BinaryAccumulate.pairs xs acc) ++ [true] := by
      simp [BinaryAccumulate.sumWord, BinaryAdd.result, hov, BinaryAdd.carryWord]
    have hl : (BinaryAccumulate.pairs xs acc).length = BinaryAccumulate.width xs acc := by
      simp [BinaryAccumulate.pairs, BinaryAccumulate.padded_left_length,
        BinaryAccumulate.padded_right_length]
    rw [hs, value_append_true, BinaryAdd.digits_length, hl] at hv
    omega

variable (twoS twoT R0 : List Bool) (hS : value twoS ≤ value twoT) (hR : value R0 < value twoT)
  (hSl : twoS.length ≤ twoT.length + 1) (hRl : R0.length ≤ twoT.length + 1)

include hS hSl in
theorem sum_length_le (r : List Bool) (hr : value r < value twoT) (hrl : r.length ≤ twoT.length + 1) :
    (sumWord twoS r).length ≤ twoT.length + 1 := by
  have hT := Counter.value_lt twoT
  rcases Nat.lt_or_ge (BinaryAccumulate.width twoS r) (twoT.length + 1) with h | h
  · have := BinaryAccumulate.sumWord_length_le twoS r
    omega
  · have hw : BinaryAccumulate.width twoS r = twoT.length + 1 :=
      le_antisymm (max_le hSl hrl) h
    rw [sumWord_length_of_lt _ _ (by rw [hw, pow_succ]; omega), hw]

include hS hR hSl hRl in
/-- The counter stays below the modulus, within one bit of its width, and so
does the sum before reduction. -/
theorem rWord_inv (i : ℕ) :
    value (rWord twoS twoT R0 i) < value twoT ∧ (rWord twoS twoT R0 i).length ≤ twoT.length + 1 ∧
      (sumWord twoS (rWord twoS twoT R0 i)).length ≤ twoT.length + 1 := by
  induction i with
  | zero => exact ⟨hR, hRl, sum_length_le twoS twoT hS hSl R0 hR hRl⟩
  | succ i ih =>
    obtain ⟨hv, hl, hsl⟩ := ih
    have hsum := BinaryAccumulate.sumWord_value twoS (rWord twoS twoT R0 i)
    have hnext : value (rWord twoS twoT R0 (i + 1)) < value twoT ∧
        (rWord twoS twoT R0 (i + 1)).length ≤ twoT.length + 1 := by
      rw [rWord]
      split_ifs with h
      · refine ⟨?_, ?_⟩
        · rw [BinaryDecrease.diffWord_value _ _ h]; omega
        · rw [BinaryDecrease.diffWord_length, BinaryCompare.width]; omega
      · exact ⟨by omega, hsl⟩
    exact ⟨hnext.1, hnext.2, sum_length_le twoS twoT hS hSl _ hnext.1 hnext.2⟩

include hS hR hSl hRl in
/-- The counter's value is the running sum modulo the modulus. -/
theorem rWord_value (i : ℕ) :
    value (rWord twoS twoT R0 i) = (value R0 + value twoS * i) % value twoT := by
  induction i with
  | zero => simp [rWord, Nat.mod_eq_of_lt hR]
  | succ i ih =>
    have hmod : ∀ A : ℕ, (A + value twoS) % value twoT = (A % value twoT + value twoS) % value twoT :=
      fun A => (Nat.mod_add_mod A (value twoT) (value twoS)).symm
    rw [Nat.mul_succ, ← add_assoc, hmod, ← ih]
    obtain ⟨hv, -, -⟩ := rWord_inv twoS twoT R0 hS hR hSl hRl i
    have hsum := BinaryAccumulate.sumWord_value twoS (rWord twoS twoT R0 i)
    rw [rWord]
    split_ifs with h
    · rw [BinaryDecrease.diffWord_value _ _ h, hsum, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hsum, Nat.mod_eq_of_lt (by omega)]
      omega

include hS hR hSl hRl in
/-- Record `i` is selected exactly when the running sum crosses a multiple of
the modulus. -/
theorem sel_eq (i : ℕ) :
    sel twoS twoT R0 i =
      decide (value twoT ≤ (value R0 + value twoS * i) % value twoT + value twoS) := by
  rw [sel, BinaryAccumulate.sumWord_value, rWord_value twoS twoT R0 hS hR hSl hRl i]
  by_cases h : value twoT ≤ (value R0 + value twoS * i) % value twoT + value twoS
  · have h' : ¬ value twoS + (value R0 + value twoS * i) % value twoT < value twoT := by omega
    simp [h, h']
  · have h' : value twoS + (value R0 + value twoS * i) % value twoT < value twoT := by omega
    simp [h, h']

end Invariant

section Loop

/-- The bank before record `i`. -/
def X (recs : List (List (Fin (a + 4)))) (twoS twoT R0 : List Bool) (pO pR pS pT pF : ℤ) (i : ℕ) :
    Tapes 6 a :=
  bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i)))
    (putWord (fun _ => blank) pR ((rWord twoS twoT R0 i).map bitSymbol))
    (putWord (fun _ => blank) pS (twoS.map bitSymbol)) (putWord (fun _ => blank) pT (twoT.map bitSymbol))
    (fun _ => blank) (start recs i) (pO + (flat (selected recs twoS twoT R0 i)).length) pR pS pT pF

/-- The per-record cost bound: the record length plus a fixed multiple of the
modulus width. -/
def bodyBound (L r : ℕ) : ℕ := r + 10 * L + 50

theorem selected_succ (recs : List (List (Fin (a + 4)))) (S T R0 : List Bool) (i : ℕ) :
    selected recs S T R0 (i + 1) = selected recs S T R0 i ++ (if sel S T R0 i then [recs.getD i []] else []) :=
  rfl

variable (recs : List (List (Fin (a + 4)))) (twoS twoT R0 : List Bool) (pO pR pS pT pF : ℤ)
  (hS : value twoS ≤ value twoT) (hR : value R0 < value twoT)
  (hSl : twoS.length ≤ twoT.length + 1) (hRl : R0.length ≤ twoT.length + 1)

include hS hR hSl hRl in
/-- One iteration carries the bank before record `i` to the bank before record `i + 1`. -/
theorem body_hoare (i : ℕ) (hi : i < recs.length) (hnb : ∀ x ∈ recs.getD i [], x ≠ blank) :
    HoareTime body (fun v => v = X recs twoS twoT R0 pO pR pS pT pF i)
      (fun v => v = X recs twoS twoT R0 pO pR pS pT pF (i + 1))
      (bodyBound twoT.length (recs.getD i []).length) := by
  obtain ⟨c1, hp, hc1⟩ := prefix_hoare recs twoS twoT R0 pO pR pS pT pF i
  obtain ⟨c2, hk, hc2⟩ := skip_hoare recs twoS twoT R0 pO pR pS pT pF i hi hnb
  obtain ⟨c3, hc, hc3⟩ := copy_hoare recs twoS twoT R0 pO pR pS pT pF i hi hnb
  obtain ⟨-, hl, hsl⟩ := rWord_inv twoS twoT R0 hS hR hSl hRl i
  have hread : (bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)).reads 5 =
      bitSymbol (decide (value (sumWord twoS (rWord twoS twoT R0 i)) < value twoT)) := by
    simp [Tapes.reads, bank, BinaryCompare.resultWord, putWord]
  have hcost : c1 + 1 + (max c2 c3 + 1) ≤ bodyBound twoT.length (recs.getD i []).length := by
    unfold prefix_hoareBound at hc1
    unfold skip_hoareBound at hc2
    unfold copy_hoareBound at hc3
    unfold bodyBound
    have hw1 : BinaryAccumulate.width twoS (rWord twoS twoT R0 i) ≤ twoT.length + 1 :=
      max_le hSl hl
    have hw2 : BinaryCompare.width (sumWord twoS (rWord twoS twoT R0 i)) twoT ≤ twoT.length + 1 :=
      max_le hsl (by omega)
    omega
  cases hlt : decide (value (sumWord twoS (rWord twoS twoT R0 i)) < value twoT)
  · have hsel : sel twoS twoT R0 i = true := by simp [sel, hlt]
    have hcond : HoareTime condPart (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)) (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i) ++ recs.getD i [])) (putWord (fun _ => blank) pR ((diffWord twoT (sumWord twoS (rWord twoS twoT R0 i))).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) ((fun _ => blank)) ((start recs (i + 1) : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length + ↑(recs.getD i []).length + 1) (pR) (pS) (pT) (pF)) (max c2 c3 + 1) := by
      unfold condPart
      refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_)
        (hc.consequence (fun v hv => hv.1) (fun v hv => hv) le_rfl)
      exfalso
      rw [hv, hread, hlt] at hv'
      simp [bitSymbol] at hv'
    refine (hp.seq hcond).consequence (fun v hv => hv) (fun v hv => ?_) hcost
    rw [hv]
    simp only [X, selected_succ, hsel, ↓reduceIte, rWord_succ, flat_append, flat_singleton,
      ← List.append_assoc, putWord_blank_snoc, List.length_append, List.length_singleton]
    push_cast
    ring_nf
  · have hsel : sel twoS twoT R0 i = false := by simp [sel, hlt]
    have hcond : HoareTime condPart (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) (putWord (fun _ => blank) pF (BinaryCompare.resultWord (sumWord twoS (rWord twoS twoT R0 i)) twoT)) ((start recs i : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)) (fun v => v = bank (inTape recs) (putWord (fun _ => blank) pO (flat (selected recs twoS twoT R0 i))) (putWord (fun _ => blank) pR ((sumWord twoS (rWord twoS twoT R0 i)).map bitSymbol)) (putWord (fun _ => blank) pS ((twoS).map bitSymbol)) (putWord (fun _ => blank) pT ((twoT).map bitSymbol)) ((fun _ => blank)) ((start recs (i + 1) : ℤ)) (pO + ↑(flat (selected recs twoS twoT R0 i)).length) (pR) (pS) (pT) (pF)) (max c2 c3 + 1) := by
      unfold condPart
      refine branch_hoare _ (hk.consequence (fun v hv => hv.1) (fun v hv => hv) le_rfl)
        (fun v ⟨hv, hv'⟩ => ?_)
      exfalso
      rw [hv, hread, hlt] at hv'
      simp [bitSymbol] at hv'
    refine (hp.seq hcond).consequence (fun v hv => hv) (fun v hv => ?_) hcost
    rw [hv]
    simp only [X, selected_succ, hsel, Bool.false_eq_true, ↓reduceIte, rWord_succ, List.append_nil]

include hS hR hSl hRl in
/-- The selection machine: one pass over the records, each costing its length
plus a fixed multiple of the modulus width. -/
theorem select_hoare (hrec : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) :
    HoareTime (program (a := a)) (fun v => v = X recs twoS twoT R0 pO pR pS pT pF 0)
      (fun v => v = X recs twoS twoT R0 pO pR pS pT pF recs.length)
      (∑ i ∈ Finset.range recs.length, (bodyBound twoT.length (recs.getD i []).length + 2)) := by
  have hmem : ∀ i, i < recs.length → recs.getD i [] ∈ recs := fun i hi => by
    rw [getD_eq _ _ hi]; exact List.getElem_mem hi
  refine while_chain_hoare body test (X recs twoS twoT R0 pO pR pS pT pF)
    (fun i => bodyBound twoT.length (recs.getD i []).length) recs.length
    (fun i hi => body_hoare recs twoS twoT R0 pO pR pS pT pF hS hR hSl hRl i hi (hrec _ (hmem i hi)).2)
    (fun i hi => ?_) ?_
  · simp only [test, X, Tapes.reads, bank, ↓reduceIte, decide_eq_true_eq]
    exact inTape_start recs i hi (hrec _ (hmem i hi)).1 (hrec _ (hmem i hi)).2
  · simp [test, X, Tapes.reads, bank, inTape_end]

theorem sum_getD_length : ∑ i ∈ Finset.range recs.length, (recs.getD i []).length ≤ (flat recs).length := by
  induction recs with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Finset.sum_range_succ', flat_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_append, List.length_cons]
    omega

/-- The closed cost: the input volume plus a fixed multiple of the modulus
width per record. -/
theorem cost_le :
    ∑ i ∈ Finset.range recs.length, (bodyBound twoT.length (recs.getD i []).length + 2) ≤
      (flat recs).length + recs.length * (10 * twoT.length + 52) := by
  have h := sum_getD_length recs
  simp only [bodyBound, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  nlinarith

end Loop

end IntegerMultBounds.Machine.OrderedSelect
