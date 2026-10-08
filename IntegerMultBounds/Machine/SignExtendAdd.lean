import IntegerMultBounds.Machine.BinaryAccumulate
import IntegerMultBounds.Machine.TwosComplement

/-! Add a two's complement word into a wider accumulator, sign-extending the
addend and dropping the final carry. Two tapes and four states (carry and
the last addend bit): one transition per accumulator cell; the addend head
advances over its bits and parks on its blank, the accumulator head parks on
its blank, and the accumulator holds the sum modulo `2^n`. -/

namespace IntegerMultBounds.Machine.SignExtendAdd

open BinaryPad (inputSymbol outputBit)
open BinaryAdd (sumBit carryBit digits)
open TwosComplement (extTo addMod)

variable {a : ℕ}

/-- A bit symbol. -/
def isBit (x : Fin (a + 4)) : Prop := x = bitSymbol false ∨ x = bitSymbol true

instance (x : Fin (a + 4)) : Decidable (isBit x) := by unfold isBit; infer_instance

/-- The state for a carry and a last addend bit. -/
def st (c s : Bool) : Fin 4 := if s then (if c then 3 else 2) else (if c then 1 else 0)

def program (a : ℕ) : Program 2 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    let c := decide (state = 1 ∨ state = 3)
    let s := decide (state = 2 ∨ state = 3)
    if isBit (symbols 1) then
      let x := if isBit (symbols 0) then decide (symbols 0 = bitSymbol true) else s
      let y := decide (symbols 1 = bitSymbol true)
      some (st (carryBit c x y) x, fun i =>
        if i = 1 then (bitSymbol (sumBit c x y), .right)
        else (symbols i, if isBit (symbols i) then .right else .stay))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (state : Fin 4) : Config 2 4 a where
  state := state
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

/-- The addend head moves only over an actual bit. -/
def shift (x : Option Bool) : ℤ := if x = none then 0 else 1

private theorem column_step (c s : Bool) (x : Option Bool) (y : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = bitSymbol y) :
    step (program a) (cfg f g p q (st c s)) =
      some (cfg f (Function.update g q (bitSymbol (sumBit c (x.getD s) y)))
        (p + shift x) (q + 1) (st (carryBit c (x.getD s) y) (x.getD s))) := by
  have ht : (program a).transition (st c s)
      (fun i => (cfg f g p q (st c s)).tape i ((cfg f g p q (st c s)).head i)) =
      some (st (carryBit c (x.getD s) y) (x.getD s), fun i =>
        if i = 1 then (bitSymbol (sumBit c (x.getD s) y), Move.right)
        else ((cfg f g p q (st c s)).tape i ((cfg f g p q (st c s)).head i),
          if x = none then Move.stay else Move.right)) := by
    cases c <;> cases s <;> rcases x with _ | x <;> (try cases x) <;> cases y <;>
      simp [program, cfg, st, carryBit, sumBit, isBit, hx, hy, inputSymbol, blank, bitSymbol]
    all_goals (funext i; fin_cases i <;> simp [hx, hy, inputSymbol, isBit, blank, bitSymbol])
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> rcases x with _ | x <;> simp [shift]
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

/-- The columns of the extended addition, with the carry and last bit threaded. -/
def ext : Bool → Bool → List Bool → List Bool → List Bool × Bool × Bool
  | c, s, _, [] => ([], c, s)
  | c, s, [], y :: acc => ((sumBit c s y) :: (ext (carryBit c s y) s [] acc).1, (ext (carryBit c s y) s [] acc).2)
  | c, s, x :: xs, y :: acc => ((sumBit c x y) :: (ext (carryBit c x y) x xs acc).1, (ext (carryBit c x y) x xs acc).2)

theorem ext_digits (c s : Bool) (xs acc : List Bool) (h : xs.length ≤ acc.length) :
    (ext c s xs acc).1 = digits c ((xs ++ List.replicate (acc.length - xs.length) (xs.getLastD s)).zip acc) := by
  induction acc generalizing xs c s with
  | nil => cases xs <;> simp [ext, digits] at h ⊢
  | cons y acc ih =>
    cases xs with
    | nil => simp [ext, digits, List.replicate_succ, ih (carryBit c s y) s [] (by simp)]
    | cons x xs =>
      simp only [ext, List.cons_append, List.length_cons, Nat.add_sub_add_right, List.getLastD_cons,
        List.zip_cons_cons, digits]
      rw [ih (carryBit c x y) x xs (by simpa using h)]

/-- One transition per accumulator cell. -/
theorem columns_run (c s : Bool) (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (h : xs.length ≤ acc.length) (hf : f (p + xs.length) = blank) :
    run (program a) acc.length
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q (st c s)) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q ((ext c s xs acc).1.map bitSymbol))
        (p + xs.length) (q + acc.length) (st (ext c s xs acc).2.1 (ext c s xs acc).2.2)) := by
  induction acc generalizing xs c s f g p q with
  | nil =>
    cases xs with
    | nil => simp [run, ext, putWord]
    | cons x xs => simp at h
  | cons y acc ih =>
    cases xs with
    | nil =>
      have hs := column_step c s none y (putWord f p ([].map bitSymbol))
        (putWord g q ((y :: acc).map bitSymbol)) p q
        (by simp only [List.map_nil, putWord, inputSymbol]; simpa using hf)
        (by rw [List.map_cons, putWord_head])
      rw [List.length_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, List.map_nil, shift,
        ↓reduceIte, add_zero, Option.getD_none]
      have hr := ih (carryBit c s y) s [] (putWord f p ([].map bitSymbol))
        (Function.update g q (bitSymbol (sumBit c s y))) p (q + 1) (by simp) hf
      simp only [List.map_nil, putWord] at hr ⊢
      rw [hr]
      simp only [ext, List.map_cons, putWord_cons, List.length_nil, Nat.cast_zero, add_zero]
      congr 2
      push_cast; ring
    | cons x xs =>
      have hs := column_step c s (some x) y (putWord f p ((x :: xs).map bitSymbol))
        (putWord g q ((y :: acc).map bitSymbol)) p q (by rw [List.map_cons, putWord_head]; rfl)
        (by rw [List.map_cons, putWord_head])
      rw [List.length_cons, add_comm, run_add, run_one, hs]
      simp only [Option.bind_some, List.map_cons, putWord_replace_head, shift, ↓reduceIte,
        reduceCtorEq, Option.getD_some]
      rw [putWord_cons f]
      have hr := ih (carryBit c x y) x xs (Function.update f p (bitSymbol x))
        (Function.update g q (bitSymbol (sumBit c x y))) (p + 1) (q + 1) (by simpa using h)
        (by rw [Function.update_of_ne (by omega), show p + 1 + (xs.length : ℤ) = p + ((x :: xs).length : ℕ) by
            simp; ring]; exact hf)
      rw [hr]
      simp only [ext, List.map_cons, putWord_cons, List.length_cons]
      congr 2
      · push_cast; ring
      · push_cast; ring

/-- The exact contract: the accumulator receives the sum modulo `2^n` of the
sign-extended addend and itself; both heads park on their blank ends. -/
theorem add_hoare (xs acc : List Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (h : xs.length ≤ acc.length) (hf : f (p + xs.length) = blank) (hg : g (q + acc.length) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0).tapes)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q ((addMod xs acc).map bitSymbol))
        (p + xs.length) (q + acc.length) 0).tapes)
      acc.length := by
  rintro v rfl
  have h0 : (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q 0).tapes.start
      (program a) = cfg (putWord f p (xs.map bitSymbol)) (putWord g q (acc.map bitSymbol)) p q (st false false) := rfl
  refine ⟨acc.length, _, le_rfl, by rw [h0, columns_run false false xs acc f g p q h hf], ?_, ?_⟩
  · have hend : putWord g q ((ext false false xs acc).1.map bitSymbol) (q + acc.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by
        simp only [List.length_map, ext_digits _ _ _ _ h, BinaryAdd.digits_length, List.length_zip,
          List.length_append, List.length_replicate]
        omega))]
      exact hg
    simp [step, program, cfg, hend, isBit, blank, bitSymbol]
  · simp only [cfg, Config.tapes, addMod, ← ext_digits _ _ _ _ h, TwosComplement.extTo]

end IntegerMultBounds.Machine.SignExtendAdd
