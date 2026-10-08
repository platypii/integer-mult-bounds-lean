import IntegerMultBounds.Machine.Hoare

/-! Literal backwards scanning to a sentinel over an arbitrary finite alphabet.
The one-state table preserves every cell and works at arbitrary integer head
positions. Tape placement supplies additional, untouched tapes. -/

namespace IntegerMultBounds.Machine.Rewind

variable {a : ℕ}

/-- Preserve each scanned symbol and move left until the sentinel is read. -/
def program (stop : Fin (a + 4)) : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if symbols 0 = stop then none else
    some (0, fun i => (symbols i, .left))

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) : Config 1 1 a :=
  ⟨0, fun _ => p, fun _ => f⟩

theorem rewind_step (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4))
    (p : ℤ) (h : f p ≠ stop) :
    step (program stop) (cfg f p) = some (cfg f (p - 1)) := by
  simp only [step, program, cfg, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem rewind_halt (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4))
    (p : ℤ) (h : f p = stop) :
    step (program stop) (cfg f p) = none := by
  simp [step, program, cfg, h]

/-- Exactly one transition per traversed cell, with no restriction on the
starting head's sign and literal preservation of the entire tape. -/
theorem rewind_run (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4))
    (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p - j) ≠ stop) :
    run (program stop) n (cfg f p) = some (cfg f (p - n)) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add,
      ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      rewind_step stop f (p - n) (h n (by omega))

theorem rewind_exact (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4))
    (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p - j) ≠ stop)
    (hend : f (p - n) = stop) :
    run (program stop) n (cfg f p) = some (cfg f (p - n)) ∧
    step (program stop) (cfg f (p - n)) = none :=
  ⟨rewind_run stop f p n h, rewind_halt stop f (p - n) hend⟩

theorem rewind_hoare (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4))
    (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p - j) ≠ stop)
    (hend : f (p - n) = stop) :
    HoareTime (program stop)
      (fun v => v = (cfg f p).tapes)
      (fun v => v = (cfg f (p - n)).tapes) n := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := rewind_exact stop f p n h hend
  exact ⟨n, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.Rewind
