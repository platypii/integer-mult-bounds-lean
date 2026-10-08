import IntegerMultBounds.Machine.ExactFrame

/-! Scan a word of flag bits and write whether any is set: two tapes, the
flag word and the key; state one remembers a set flag; on the flag word's
blank the result bit is written at the key head, which advances. The flag
word is preserved and its head ends on its blank. -/

namespace IntegerMultBounds.Machine.AnyFlag

variable {a : ℕ}

/-- State zero: none set so far; state one: a flag set; state two: halted. -/
def program : Program 2 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 2 then none
    else if symbols 0 = blank then
      some (2, fun i => if i = 1 then (bitSymbol (decide (s = 1)), .right) else (symbols i, .stay))
    else if symbols 0 = bitSymbol true then some (1, fun i => (symbols i, if i = 0 then .right else .stay))
    else some (s, fun i => (symbols i, if i = 0 then .right else .stay))

/-- The seen-flag state. -/
def seenState (b : Bool) : Fin 3 := if b then 1 else 0

def cfg (F K : ℤ → Fin (a + 4)) (pf pk : ℤ) (s : Fin 3) : Config 2 3 a :=
  ⟨s, fun i => if i = 0 then pf else pk, fun i => if i = 0 then F else K⟩

theorem bit_step (F K : ℤ → Fin (a + 4)) (pf pk : ℤ) (seen x : Bool) (hx : F pf = bitSymbol x) :
    step program (cfg F K pf pk (seenState seen)) = some (cfg F K (pf + 1) pk (seenState (seen || x))) := by
  have ht : (program (a := a)).transition (seenState seen)
      (fun i => (cfg F K pf pk (seenState seen)).tape i ((cfg F K pf pk (seenState seen)).head i)) =
      some (seenState (seen || x), fun i => ((cfg F K pf pk (seenState seen)).tape i
        ((cfg F K pf pk (seenState seen)).head i), if i = 0 then Move.right else Move.stay)) := by
    cases seen <;> cases x <;> simp [program, cfg, seenState, hx, bitSymbol, blank]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

theorem scan_run (F K : ℤ → Fin (a + 4)) (pf pk : ℤ) (seen : Bool) (fl : List Bool) :
    run program fl.length (cfg (putWord F pf (fl.map bitSymbol)) K pf pk (seenState seen)) =
      some (cfg (putWord F pf (fl.map bitSymbol)) K (pf + fl.length) pk
        (seenState (seen || fl.any id))) := by
  induction fl generalizing F pf seen with
  | nil => simp [run]
  | cons x fl ih =>
    rw [List.length_cons, List.map_cons, run, bit_step _ _ _ _ seen x (by rw [putWord_head])]
    simp only [Option.bind_some, putWord_cons]
    rw [ih (Function.update F pf (bitSymbol x)) (pf + 1) (seen || x)]
    simp only [List.any_cons, id]
    congr 2
    · push_cast; ring
    · cases seen <;> cases x <;> simp

theorem final_step (F K : ℤ → Fin (a + 4)) (pf pk : ℤ) (seen : Bool) (hf : F pf = blank) :
    step program (cfg F K pf pk (seenState seen)) =
      some (cfg F (Function.update K pk (bitSymbol seen)) pf (pk + 1) 2) := by
  have ht : (program (a := a)).transition (seenState seen)
      (fun i => (cfg F K pf pk (seenState seen)).tape i ((cfg F K pf pk (seenState seen)).head i)) =
      some (2, fun i => if i = 1 then (bitSymbol seen, Move.right)
        else ((cfg F K pf pk (seenState seen)).tape i ((cfg F K pf pk (seenState seen)).head i),
          Move.stay)) := by
    cases seen <;> simp [program, cfg, seenState, hf]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (try (intro hj; rw [hj]))

/-- The contract: the flag word is preserved with its head on its blank end;
the key receives the "any flag" bit and its head advances. -/
theorem any_hoare (F K : ℤ → Fin (a + 4)) (pf pk : ℤ) (fl : List Bool) (hf : F (pf + fl.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord F pf (fl.map bitSymbol)) K pf pk 0).tapes)
      (fun v => v = (cfg (putWord F pf (fl.map bitSymbol)) (Function.update K pk (bitSymbol (fl.any id)))
        (pf + fl.length) (pk + 1) 0).tapes)
      (fl.length + 1) := by
  rintro v rfl
  refine ⟨fl.length + 1, cfg (putWord F pf (fl.map bitSymbol)) (Function.update K pk (bitSymbol (fl.any id)))
    (pf + fl.length) (pk + 1) 2, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  have h0 : (cfg (putWord F pf (fl.map bitSymbol)) K pf pk 0).tapes.start program =
      cfg (putWord F pf (fl.map bitSymbol)) K pf pk (seenState false) := rfl
  rw [h0, run_add, scan_run]
  simp only [Option.bind_some, run_one, Bool.false_or]
  rw [final_step _ _ _ _ _ (by rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hf])]

end IntegerMultBounds.Machine.AnyFlag
