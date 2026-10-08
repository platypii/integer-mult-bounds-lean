import IntegerMultBounds.Machine.OrderedSelect

/-! Blank-separated records: the cell before a record's origin is blank, bit
words map to records, and a backward move from the origin of one record to
the origin of the previous one (four states, one transition per cell). -/

namespace IntegerMultBounds.Machine.OrderedSelect

variable {a : ℕ}

/-- The cell before a record's origin is blank. -/
theorem bg_left (recs : List (List (Fin (a + 4)))) (i : ℕ) (hi : i < recs.length) :
    bg recs i ((start recs i : ℤ) - 1) = blank := by
  unfold bg
  rw [putWord_outside _ _ _ _ (Or.inl (by omega))]
  cases i with
  | zero => rw [start_zero]; rw [putWord_outside _ _ _ _ (Or.inl (by simp))]
  | succ i =>
    have hi' : i < recs.length := by omega
    rw [take_succ_getD recs i hi', flat_append, flat_singleton, start_succ recs i hi',
      ← List.append_assoc, ← putWord_append_forward]
    have hs : (start recs i : ℤ) = ↑(flat (recs.take i)).length := rfl
    push_cast
    rw [hs]
    have key := putWord_head (putWord (fun _ => (blank : Fin (a + 4))) 0
      (flat (recs.take i) ++ recs.getD i [])) (0 + ↑(flat (recs.take i) ++ recs.getD i []).length) blank []
    convert key using 2
    simp

theorem getD_map (ws : List (List Bool)) (i : ℕ) :
    (ws.map (List.map (bitSymbol (a := a)))).getD i [] = (ws.getD i []).map bitSymbol := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [List.length_map]; omega), List.getElem?_eq_none (by omega)]
    rfl

theorem length_map_words (ws : List (List Bool)) :
    (ws.map (List.map (bitSymbol (a := a)))).length = ws.length := List.length_map _

end IntegerMultBounds.Machine.OrderedSelect

namespace IntegerMultBounds.Machine.BackWord

variable {a : ℕ}

/-- From the cell after a record's separator, move back to the record's
origin: two steps left, scan left over the record, one step right. -/
def program : Program 1 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then some (2, fun i => (symbols i, .left))
    else if s = 2 then
      if symbols 0 = blank then some (3, fun i => (symbols i, .right))
      else some (2, fun i => (symbols i, .left))
    else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 4) : Config 1 4 a := ⟨s, fun _ => p, fun _ => f⟩

theorem step0 (f : ℤ → Fin (a + 4)) (p : ℤ) : step program (cfg f p 0) = some (cfg f (p - 1) 1) := by
  unfold step
  simp [cfg, program, Move.offset]
  refine ⟨by funext _; ring, ?_⟩
  funext _ j
  by_cases hj : j = p <;> simp [hj]

theorem step1 (f : ℤ → Fin (a + 4)) (p : ℤ) : step program (cfg f p 1) = some (cfg f (p - 1) 2) := by
  unfold step
  simp [cfg, program, Move.offset]
  refine ⟨by funext _; ring, ?_⟩
  funext _ j
  by_cases hj : j = p <;> simp [hj]

theorem step_scan (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p ≠ blank) :
    step program (cfg f p 2) = some (cfg f (p - 1) 2) := by
  unfold step
  simp [cfg, program, Move.offset, h]
  refine ⟨by funext _; ring, ?_⟩
  funext _ j
  by_cases hj : j = p <;> simp [hj]

theorem step_exit (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p = blank) :
    step program (cfg f p 2) = some (cfg f (p + 1) 3) := by
  unfold step
  simp [cfg, program, Move.offset, h]
  funext _ j
  by_cases hj : j = p <;> simp [hj, h]

theorem scan_run (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p + j) ≠ blank) :
    run program n (cfg f (p + n - 1) 2) = some (cfg f (p - 1) 2) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run, step_scan _ _ (by
      rw [show p + ↑(n + 1) - 1 = p + ↑n by push_cast; ring]; exact h n (by omega))]
    simp only [Option.bind_some]
    rw [show p + ↑(n + 1) - 1 - 1 = p + ↑n - 1 by push_cast; ring]
    exact ih (fun j hj => h j (by omega))

/-- The exact contract: from the cell after the separator of a record whose
left neighbour is blank, the head returns to the record's origin. -/
theorem back_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hleft : f (p - 1) = blank) (hsep : f (p + xs.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) (p + xs.length + 1) 0).tapes)
      (fun v => v = (cfg (putWord f p xs) p 0).tapes) (xs.length + 3) := by
  rintro v rfl
  refine ⟨xs.length + 3, cfg (putWord f p xs) p 3, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  have hbl : putWord f p xs (p - 1) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inl (by omega))]; exact hleft
  have h0 : (cfg (putWord f p xs) (p + xs.length + 1) 0).tapes.start program =
      cfg (putWord f p xs) (p + xs.length + 1) 0 := rfl
  rw [h0, show xs.length + 3 = 1 + (1 + (xs.length + 1)) by ring, run_add, run_one, step0]
  simp only [Option.bind_some, run_add, run_one]
  rw [step1]
  simp only [Option.bind_some]
  rw [show p + ↑xs.length + 1 - 1 - 1 = p + ↑xs.length - 1 by ring,
    scan_run (putWord f p xs) p xs.length (fun j hj =>
      hx _ (ReturnOrigin.putWord_mem f p xs (p + j) ⟨by omega, by omega⟩))]
  simp only [Option.bind_some]
  rw [step_exit _ _ hbl]
  congr 2
  ring

end IntegerMultBounds.Machine.BackWord
