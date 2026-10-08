import IntegerMultBounds.Machine.ExactFrame

/-! Read a bit on one tape and prepend it, or its negation, to a word on a
second tape: the second head steps left and writes the bit there, so the
word starting one cell to the right is doubled and the bit added in
least-significant-first reading. The first head optionally steps left after
reading, which consumes the bits of a word from its most significant end.
Two tapes, four states, two transitions. -/

namespace IntegerMultBounds.Machine.PrependRead

variable {a : ℕ}

/-- State one remembers a zero bit, state two a one bit, state three halts. -/
def program (move : Move) (neg : Bool) : Program 2 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 0 = bitSymbol false then
        some (1, fun i => (symbols i, if i = 0 then move else .left))
      else if symbols 0 = bitSymbol true then
        some (2, fun i => (symbols i, if i = 0 then move else .left))
      else none
    else if s = 1 then some (3, fun i => (if i = 1 then bitSymbol neg else symbols i, .stay))
    else if s = 2 then some (3, fun i => (if i = 1 then bitSymbol (!neg) else symbols i, .stay))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (s : Fin 4) : Config 2 4 a where
  state := s
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

/-- The remembered bit's state. -/
def bitState (b : Bool) : Fin 4 := if b then 2 else 1

theorem read_step (move : Move) (neg b : Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hb : f p = bitSymbol b) :
    step (program move neg) (cfg f g p q 0) = some (cfg f g (p + move.offset) (q - 1) (bitState b)) := by
  have ht : (program (a := a) move neg).transition 0
      (fun i => (cfg f g p q 0).tape i ((cfg f g p q 0).head i)) =
      some (bitState b, fun i => ((cfg f g p q 0).tape i ((cfg f g p q 0).head i),
        if i = 0 then move else Move.left)) := by
    cases b <;> simp [program, cfg, bitState, hb, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  dsimp only
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [Move.offset, sub_eq_add_neg]
  · funext i j
    fin_cases i <;> simp
    all_goals (intro hj; rw [hj])

theorem write_step (move : Move) (neg b : Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    step (program move neg) (cfg f g p q (bitState b)) =
      some (cfg f (Function.update g q (bitSymbol (xor b neg))) p q 3) := by
  have ht : (program (a := a) move neg).transition (bitState b)
      (fun i => (cfg f g p q (bitState b)).tape i ((cfg f g p q (bitState b)).head i)) =
      some (3, fun i => (if i = 1 then bitSymbol (xor b neg)
        else (cfg f g p q (bitState b)).tape i ((cfg f g p q (bitState b)).head i), Move.stay)) := by
    cases b <;> cases neg <;> simp [program, cfg, bitState]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

theorem halt (move : Move) (neg : Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    step (program move neg) (cfg f g p q 3) = none := by
  simp [step, program, cfg]

/-- Read the bit under the first head, move that head, and write the bit,
negated when asked, one cell left of the second head. -/
theorem prepend_hoare (move : Move) (neg b : Bool) (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hb : f p = bitSymbol b) :
    HoareTime (program move neg) (fun v => v = (cfg f g p q 0).tapes)
      (fun v => v = (cfg f (Function.update g (q - 1) (bitSymbol (xor b neg)))
        (p + move.offset) (q - 1) 0).tapes) 2 := by
  rintro v rfl
  refine ⟨2, cfg f (Function.update g (q - 1) (bitSymbol (xor b neg))) (p + move.offset) (q - 1) 3,
    le_rfl, ?_, halt _ _ _ _ _ _, rfl⟩
  have h0 : (cfg f g p q 0).tapes.start (program move neg) = cfg f g p q 0 := rfl
  rw [h0, run_add _ 1 1, run_one, read_step move neg b f g p q hb]
  simp only [Option.bind_some, run_one, write_step]

end IntegerMultBounds.Machine.PrependRead
