import IntegerMultBounds.Machine.SignExtendAdd

/-! In-place two's complement negation on one tape: copy bits up to and
including the first one, then complement; halt on the blank. One transition
per bit; the head parks on the word's blank end. -/

namespace IntegerMultBounds.Machine.Negate

open SignExtendAdd (isBit)
open TwosComplement (negWord)

variable {a : ℕ}

/-- State zero before the first one bit, one after it. -/
def stN (b : Bool) : Fin 2 := if b then 1 else 0

def program (a : ℕ) : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if isBit (symbols 0) then
      let b := decide (symbols 0 = bitSymbol true)
      if state = 0 then some (stN b, fun _ => (bitSymbol b, .right))
      else some (1, fun _ => (bitSymbol (!b), .right))
    else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 2) : Config 1 2 a := ⟨s, fun _ => p, fun _ => f⟩

/-- Negation from a given state: bits are copied until a one has been seen. -/
def negFrom : Bool → List Bool → List Bool
  | _, [] => []
  | false, b :: bs => b :: negFrom b bs
  | true, b :: bs => (!b) :: negFrom true bs

theorem negFrom_true (bs : List Bool) : negFrom true bs = bs.map not := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [negFrom, ih]

theorem negFrom_false (bs : List Bool) : negFrom false bs = negWord bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [negFrom, negWord, ih, negFrom_true]

theorem bit_step (f : ℤ → Fin (a + 4)) (p : ℤ) (s b : Bool) (hb : f p = bitSymbol b) :
    step (program a) (cfg f p (stN s)) =
      some (cfg (Function.update f p (bitSymbol (if s then !b else b))) (p + 1) (stN (s || b))) := by
  have hsym : (fun i : Fin 1 => (cfg f p (stN s)).tape i ((cfg f p (stN s)).head i)) =
      fun _ => bitSymbol b := by
    funext i; simp [cfg, hb]
  unfold step
  rw [hsym]
  cases s <;> cases b <;> simp [program, stN, isBit, bitSymbol, blank, cfg, Move.offset] <;>
    (funext i j; by_cases hj : j = p
     · subst j; simp
     · simp [hj])

theorem neg_run (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Bool) (bs : List Bool) :
    run (program a) bs.length (cfg (putWord f p (bs.map bitSymbol)) p (stN s)) =
      some (cfg (putWord f p ((negFrom s bs).map bitSymbol)) (p + bs.length) (stN (s || bs.any id))) := by
  induction bs generalizing f p s with
  | nil => simp [run, negFrom]
  | cons b bs ih =>
    rw [List.length_cons, add_comm, run_add, run_one, List.map_cons,
      bit_step _ _ s b (putWord_head _ _ _ _)]
    simp only [Option.bind_some, putWord_replace_head]
    rw [ih]
    cases s <;> cases b <;> simp [negFrom, putWord_cons, List.any_cons] <;> ring_nf

/-- The exact contract: the word is replaced by its two's complement negation
and the head parks on its blank end. -/
theorem neg_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) (bs : List Bool) (hf : f (p + bs.length) = blank) :
    HoareTime (program a) (fun v => v = (cfg (putWord f p (bs.map bitSymbol)) p 0).tapes)
      (fun v => v = (cfg (putWord f p ((negWord bs).map bitSymbol)) (p + bs.length) 0).tapes)
      bs.length := by
  rintro v rfl
  have h0 : (cfg (putWord f p (bs.map bitSymbol)) p 0).tapes.start (program a) =
      cfg (putWord f p (bs.map bitSymbol)) p (stN false) := rfl
  refine ⟨bs.length, _, le_rfl, by rw [h0, neg_run], ?_, ?_⟩
  · have hend : putWord f p ((negFrom false bs).map bitSymbol) (p + bs.length) = blank := by
      rw [putWord_outside _ _ _ _ (Or.inr (by simp [negFrom_false, TwosComplement.negWord_length]))]
      exact hf
    simp [step, program, cfg, hend, isBit, blank, bitSymbol]
  · simp only [cfg, Config.tapes, negFrom_false]

end IntegerMultBounds.Machine.Negate
