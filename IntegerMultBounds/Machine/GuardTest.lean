import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.WordMoves

/-! Comparing a fixed number of cells of a word with a constant word, the
order kept in a single cell: for each cell the two heads advance and the
order cell is updated, a later column overriding the order so far; then a
flag bit, whether the order is "smaller" or "larger" as requested, is
appended to a flag word and the order cell is erased. Unrolled into finite
control. The order semantics are those of `BinaryCompare.rel`. -/

namespace IntegerMultBounds.Machine.GuardTest

variable {a : ℕ}

open BinaryCompare (cmpBit rel)
open Gather (field)

/-- The order as a cell symbol: blank for equal, the bits for smaller and larger. -/
def ordSymbol : Ordering → Fin (a + 4)
  | .eq => blank
  | .lt => bitSymbol false
  | .gt => bitSymbol true

/-- The order read back from a cell. -/
def symbolOrd (x : Fin (a + 4)) : Ordering :=
  if x = bitSymbol false then .lt else if x = bitSymbol true then .gt else .eq

theorem symbolOrd_ordSymbol (o : Ordering) : symbolOrd (ordSymbol (a := a) o) = o := by
  cases o <;> simp [symbolOrd, ordSymbol, bitSymbol, blank]

/-- Three tapes: the word, the constant, the order cell. One column:
read both bits, update the order cell, advance both word heads. -/
def cmpCell (a : ℕ) : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      some (1, fun i =>
        (if i = 2 then ordSymbol (cmpBit (symbolOrd (symbols 2))
          (decide (symbols 0 = bitSymbol true)) (decide (symbols 1 = bitSymbol true)))
        else symbols i, if i = 2 then .stay else .right))
    else none

/-- The three-tape bank: word, constant, order cell. -/
def bank (f g h : ℤ → Fin (a + 4)) (px pc po : ℤ) : Tapes 3 a :=
  ⟨fun i => if i = 0 then px else if i = 1 then pc else po,
   fun i => if i = 0 then f else if i = 1 then g else h⟩

theorem cmpCell_hoare (f g h : ℤ → Fin (a + 4)) (px pc po : ℤ) (x y : Bool) (o : Ordering)
    (hx : f px = bitSymbol x) (hy : g pc = bitSymbol y) (ho : h po = ordSymbol o) :
    HoareTime (cmpCell a) (fun v => v = bank f g h px pc po)
      (fun v => v = bank f g (Function.update h po (ordSymbol (cmpBit o x y))) (px + 1) (pc + 1) po) 1 := by
  rintro v rfl
  refine ⟨1, ⟨1, (bank f g (Function.update h po (ordSymbol (cmpBit o x y))) (px + 1) (pc + 1) po).head,
    (bank f g (Function.update h po (ordSymbol (cmpBit o x y))) (px + 1) (pc + 1) po).tape⟩, le_rfl, ?_,
    by simp [step, cmpCell], rfl⟩
  rw [run_one]
  have hx' : decide (f px = bitSymbol true) = x := by rw [hx]; cases x <;> simp [bitSymbol]
  have hy' : decide (g pc = bitSymbol true) = y := by rw [hy]; cases y <;> simp [bitSymbol]
  simp only [step, cmpCell, Tapes.start, bank, ↓reduceIte, hx', Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    by_cases hj : j = po
    · subst hj
      fin_cases i <;> simp [ho, symbolOrd_ordSymbol, hy']
      all_goals (try (intro hj'; rw [hj']))
    · fin_cases i <;> simp [Function.update_apply, hj]
      all_goals (try (intro hj'; rw [hj']))

theorem rel_append_singleton (o : Ordering) (cols : List (Bool × Bool)) (x y : Bool) :
    rel o (cols ++ [(x, y)]) = cmpBit (rel o cols) x y := by
  induction cols generalizing o with
  | nil => rfl
  | cons c rest ih => rcases c with ⟨cx, cy⟩; simp [rel, ih]

/-- The order cell after `d` columns from a start order: the word's field
from `start` against the constant's first `d` bits. -/
def orderAfter (o : Ordering) (xs ys : List Bool) (start d : ℕ) : Ordering :=
  rel o ((field xs start d).zip (field ys 0 d))

@[simp] theorem orderAfter_zero (o : Ordering) (xs ys : List Bool) (start : ℕ) :
    orderAfter o xs ys start 0 = o := rfl

theorem orderAfter_succ (o : Ordering) (xs ys : List Bool) (start d : ℕ) :
    orderAfter o xs ys start (d + 1) =
      cmpBit (orderAfter o xs ys start d) (xs.getD (start + d) false) (ys.getD d false) := by
  simp only [orderAfter, Gather.field_succ, zero_add]
  rw [List.zip_append (by simp), List.zip_cons_cons, List.zip_nil_right, rel_append_singleton]

/-- `d` columns: the word head advances `d` cells from `px + start`, the
constant head `d` cells from its origin, the order cell records the order. -/
theorem cmpCells_hoare (d : ℕ) (o : Ordering) (xs ys : List Bool) (f g h : ℤ → Fin (a + 4))
    (px pc po : ℤ) (start : ℕ) (hx : start + d ≤ xs.length) (hy : d ≤ ys.length) :
    HoareTime (iterate (cmpCell a) d)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        (Function.update h po (ordSymbol o)) (px + start) pc po)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        (Function.update h po (ordSymbol (orderAfter o xs ys start d))) (px + start + d) (pc + d) po)
      (d * (1 + 1)) := by
  have hit := iterate_hoare (cmpCell a) d (fun j => bank (putWord f px (xs.map bitSymbol))
    (putWord g pc (ys.map bitSymbol)) (Function.update h po (ordSymbol (orderAfter o xs ys start j)))
    (px + start + j) (pc + j) po) 1 (fun j hj => by
      have hc := cmpCell_hoare (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        (Function.update h po (ordSymbol (orderAfter o xs ys start j))) (px + start + j) (pc + j) po
        (xs.getD (start + j) false) (ys.getD j false) (orderAfter o xs ys start j)
        (by rw [show px + (start : ℤ) + j = px + ((start + j : ℕ) : ℤ) by push_cast; ring,
          Gather.putWord_getD _ _ _ _ (by omega)])
        (by rw [Gather.putWord_getD _ _ _ _ (by omega)]) (by simp)
      refine hc.consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
      rw [hv, Function.update_idem, ← orderAfter_succ]
      congr 1 <;> push_cast <;> ring)
  simpa using hit

/-- Two tapes: the order cell and the flag word. Append the flag, whether the
order is the target, and erase the order cell. -/
def flagCell (target : Ordering) (a : ℕ) : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      some (1, fun i =>
        if i = 0 then (blank, .stay)
        else (bitSymbol (decide (symbolOrd (symbols 0) = target)), .right))
    else none

/-- The two-tape bank: order cell, flag word. -/
def bank2 (h F : ℤ → Fin (a + 4)) (po pf : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then po else pf, fun i => if i = 0 then h else F⟩

theorem flagCell_hoare (target : Ordering) (h F : ℤ → Fin (a + 4)) (po pf : ℤ) (o : Ordering) :
    HoareTime (flagCell target a)
      (fun v => v = bank2 (Function.update h po (ordSymbol o)) F po pf)
      (fun v => v = bank2 (Function.update h po blank)
        (Function.update F pf (bitSymbol (decide (o = target)))) po (pf + 1)) 1 := by
  rintro v rfl
  refine ⟨1, ⟨1, (bank2 (Function.update h po blank)
    (Function.update F pf (bitSymbol (decide (o = target)))) po (pf + 1)).head,
    (bank2 (Function.update h po blank)
    (Function.update F pf (bitSymbol (decide (o = target)))) po (pf + 1)).tape⟩, le_rfl, ?_,
    by simp [step, flagCell], rfl⟩
  rw [run_one]
  simp only [step, flagCell, Tapes.start, bank2, ↓reduceIte, Function.update_self,
    symbolOrd_ordSymbol, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (try split_ifs <;> simp_all)

end IntegerMultBounds.Machine.GuardTest
