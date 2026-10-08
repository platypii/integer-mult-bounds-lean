import IntegerMultBounds.Machine.KeySelect

/-! A literal unary-selector increment. The selector is scanned to its blank,
extended by one symbol, and rewound to zero. A second tape's head advances by
one at the write step while its entire contents are preserved. -/

namespace IntegerMultBounds.Machine.UnarySelector

open PartitionMarked

def program : Program 2 3 1 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 2 then none
    else if state = 0 then
      if symbols 0 = blank then
        some (1, fun i => if i = 0 then (bitSymbol true, .left) else (symbols i, .right))
      else some (0, fun i => (symbols i, if i = 0 then .right else .stay))
    else if symbols 0 = marker then
      some (2, fun i => (symbols i, if i = 0 then .right else .stay))
    else some (1, fun i => (symbols i, if i = 0 then .left else .stay))

def cfg (f limit : ℤ → Fin 5) (p q : ℤ) (state : Fin 3) : Config 2 3 1 where
  state := state
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else limit

/-- Extending the selector at its blank endpoint gives exactly the next unary
word, including its left sentinel and globally blank suffix. -/
theorem selector_succ (k : ℕ) :
    Function.update (KeySelect.selector k) (k : ℤ) (bitSymbol true) = KeySelect.selector (k + 1) := by
  funext j
  by_cases hj : j = k
  · subst j
    simp only [Function.update_self]
    symm
    exact KeySelect.selector_inside (k + 1) k (by omega)
  · rw [Function.update_of_ne hj]
    unfold KeySelect.selector
    have hi : (0 ≤ j ∧ j < (k : ℤ)) ↔ (0 ≤ j ∧ j < ((k + 1 : ℕ) : ℤ)) := by omega
    simp only [hi]

private theorem right_step (f limit : ℤ → Fin 5) (p q : ℤ) (h : f p ≠ blank) :
    step program (cfg f limit p q 0) = some (cfg f limit (p + 1) q 0) := by
  simp only [step, program, cfg, show (0 : Fin 3) ≠ 2 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

private theorem write_step (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) :
    step program (cfg (KeySelect.selector k) limit k q 0) =
      some (cfg (KeySelect.selector (k + 1)) limit (k - 1 : ℤ) (q + 1) 1) := by
  simp only [step, program, cfg, show (0 : Fin 3) ≠ 2 by decide, ↓reduceIte,
    KeySelect.selector_end, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [sub_eq_add_neg]
  · funext i j
    fin_cases i
    · change (if j = (k : ℤ) then bitSymbol true else KeySelect.selector k j) = _
      have hs := congrFun (selector_succ k) j
      simpa [Function.update_apply, eq_comm] using hs
    · simp; intro hj; rw [hj]

private theorem left_step (f limit : ℤ → Fin 5) (p q : ℤ) (h : f p ≠ marker) :
    step program (cfg f limit p q 1) = some (cfg f limit (p - 1) q 1) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [sub_eq_add_neg]
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

private theorem finish_step (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) :
    step program (cfg (KeySelect.selector k) limit (-1) q 1) =
      some (cfg (KeySelect.selector k) limit 0 q 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, KeySelect.selector_left, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j; fin_cases i <;> simp <;> intro hj <;> simp [hj]

private theorem right_run (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) (n : ℕ) (hn : n ≤ k) :
    run program n (cfg (KeySelect.selector k) limit 0 q 0) =
      some (cfg (KeySelect.selector k) limit n q 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add, ih (by omega)]
    simp only [Option.bind_some, run_one]
    have hs := right_step (KeySelect.selector k) limit n q
      (by rw [KeySelect.selector_inside k n (by omega)]; decide)
    simpa only [Nat.cast_add, Nat.cast_one] using hs

private theorem left_run (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) (p : ℤ) (n : ℕ)
    (hn : ∀ j : ℕ, j < n → p - j ≠ -1) :
    run program n (cfg (KeySelect.selector k) limit p q 1) =
      some (cfg (KeySelect.selector k) limit (p - n) q 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => hn j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      left_step (KeySelect.selector k) limit (p - n) q (KeySelect.selector_ne_marker k _ (hn n (by omega)))

/-- Every increment takes exactly two times the current selector length plus
two transitions. The width tape's cursor moves once; all its cells survive. -/
theorem increment_exact (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) :
    run program (2 * k + 2) (cfg (KeySelect.selector k) limit 0 q 0) =
      some (cfg (KeySelect.selector (k + 1)) limit 0 (q + 1) 2) ∧
    step program (cfg (KeySelect.selector (k + 1)) limit 0 (q + 1) 2) = none := by
  have hr := right_run k limit q k le_rfl
  have hw := write_step k limit q
  have hl := left_run (k + 1) limit (q + 1) (k - 1 : ℤ) k (by intro j hj; omega)
  have hp : (k : ℤ) - 1 - k = -1 := by omega
  rw [hp] at hl
  have hf := finish_step (k + 1) limit (q + 1)
  refine ⟨?_, ?_⟩
  · rw [show 2 * k + 2 = (k + 1) + k + 1 by omega, run_add, run_add, run_add, hr]
    simp only [Option.bind_some, run_one, hw, hl, hf]
  · simp [step, program, cfg]

theorem increment_hoare (k : ℕ) (limit : ℤ → Fin 5) (q : ℤ) :
    HoareTime program
      (fun v => v = (cfg (KeySelect.selector k) limit 0 q 0).tapes)
      (fun v => v = (cfg (KeySelect.selector (k + 1)) limit 0 (q + 1) 2).tapes)
      (2 * k + 2) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := increment_exact k limit q
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.UnarySelector
