import IntegerMultBounds.Machine.WordMoves

/-! Advance a data head by the length of a ruler word: two tapes and one
state step right together while the ruler reads nonblank. One transition per
ruler cell; the ruler head parks on the ruler's blank end. -/

namespace IntegerMultBounds.Machine.RulerAdvance

variable {a : ℕ}

def program : Program 2 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank then none else some (0, fun i => (symbols i, .right))

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) : Config 2 1 a :=
  ⟨0, fun i => if i = 0 then p else q, fun i => if i = 0 then f else g⟩

theorem advance_step (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p ≠ blank) :
    step program (cfg f g p q) = some (cfg f g (p + 1) (q + 1)) := by
  unfold step
  simp only [cfg, program, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

theorem advance_run (f g : ℤ → Fin (a + 4)) (p q : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p + j) ≠ blank) :
    run program n (cfg f g p q) = some (cfg f g (p + n) (q + n)) := by
  induction n generalizing p q with
  | zero => simp [run]
  | succ n ih =>
    rw [add_comm, run_add, run_one, advance_step _ _ _ _ (by simpa using h 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (p + 1) (q + 1) (fun j hj => by
      rw [show p + 1 + (j : ℤ) = p + ((j + 1 : ℕ) : ℤ) by push_cast; ring]
      exact h (j + 1) (by omega))]
    congr 2 <;> push_cast <;> ring

/-- The exact contract: both heads advance by the ruler's length and the
ruler head parks on its blank end. -/
theorem advance_hoare (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hend : f (p + xs.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) g p q).tapes)
      (fun v => v = (cfg (putWord f p xs) g (p + xs.length) (q + xs.length)).tapes) xs.length := by
  rintro v rfl
  refine ⟨xs.length, _, le_rfl, ?_, ?_, rfl⟩
  · exact advance_run (putWord f p xs) g p q xs.length (fun j hj =>
      hx _ (ReturnOrigin.putWord_mem f p xs (p + j) ⟨by omega, by omega⟩))
  · simp [step, program, cfg, putWord_outside _ _ _ _ (Or.inr (le_refl _)), hend]

end IntegerMultBounds.Machine.RulerAdvance

namespace IntegerMultBounds.Machine.RulerRetreat

variable {a : ℕ}

/-- Retreat both heads by the ruler's length: from the ruler's blank end,
step both heads left while the ruler reads nonblank, then one step right. -/
def program : Program 2 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then
      if symbols 0 = blank then some (2, fun i => (symbols i, .right))
      else some (1, fun i => (symbols i, .left))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (s : Fin 3) : Config 2 3 a :=
  ⟨s, fun i => if i = 0 then p else q, fun i => if i = 0 then f else g⟩

theorem step_start (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    step program (cfg f g p q 0) = some (cfg f g (p - 1) (q - 1) 1) := by
  unfold step
  simp only [cfg, program, ↓reduceIte, Move.offset, Fin.isValue]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp <;> ring
  · funext i j
    fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

theorem step_left (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p ≠ blank) :
    step program (cfg f g p q 1) = some (cfg f g (p - 1) (q - 1) 1) := by
  unfold step
  simp only [cfg, program, h, ↓reduceIte, Move.offset, Fin.isValue, one_ne_zero]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp <;> ring
  · funext i j
    fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

theorem step_exit (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p = blank) :
    step program (cfg f g p q 1) = some (cfg f g (p + 1) (q + 1) 2) := by
  unfold step
  simp only [cfg, program, h, ↓reduceIte, Move.offset, Fin.isValue, one_ne_zero]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp
    all_goals (try (intro hj; rw [hj]))

theorem left_run (f g : ℤ → Fin (a + 4)) (p q : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p + j) ≠ blank) :
    run program n (cfg f g (p + n - 1) (q + n - 1) 1) = some (cfg f g (p - 1) (q - 1) 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run, step_left _ _ _ _ (by
      rw [show p + ↑(n + 1) - 1 = p + n by push_cast; ring]; exact h n (by omega))]
    simp only [Option.bind_some]
    rw [show p + ↑(n + 1) - 1 - 1 = p + n - 1 by push_cast; ring,
      show q + ↑(n + 1) - 1 - 1 = q + n - 1 by push_cast; ring]
    exact ih (fun j hj => h j (by omega))

/-- The exact contract: both heads retreat by the ruler's length and the
ruler head parks on the ruler's origin. -/
theorem retreat_hoare (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hleft : f (p - 1) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) g (p + xs.length) (q + xs.length) 0).tapes)
      (fun v => v = (cfg (putWord f p xs) g p q 0).tapes) (xs.length + 2) := by
  rintro v rfl
  refine ⟨xs.length + 2, cfg (putWord f p xs) g p q 2, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  have hbl : putWord f p xs (p - 1) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inl (by omega))]; exact hleft
  rw [show xs.length + 2 = 1 + (xs.length + 1) by ring, run_add, run_one]
  have h0 : (cfg (putWord f p xs) g (p + xs.length) (q + xs.length) 0).tapes.start program =
      cfg (putWord f p xs) g (p + xs.length) (q + xs.length) 0 := rfl
  rw [h0, step_start]
  simp only [Option.bind_some]
  rw [run_add, left_run (putWord f p xs) g p q xs.length (fun j hj =>
    hx _ (ReturnOrigin.putWord_mem f p xs (p + j) ⟨by omega, by omega⟩))]
  simp only [Option.bind_some, run_one]
  rw [step_exit _ _ _ _ hbl]
  congr 2 <;> ring

end IntegerMultBounds.Machine.RulerRetreat
