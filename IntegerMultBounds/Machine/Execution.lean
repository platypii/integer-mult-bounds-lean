import IntegerMultBounds.Machine

/-! Basic execution laws and a concrete one-tape scan with an exact step count.
The scan is a primitive for stream routines, not a multiplication algorithm. -/

namespace IntegerMultBounds.Machine

variable {t q a : ℕ}

theorem run_add (M : Program t q a) (n m : ℕ) (c : Config t q a) :
    run M (n + m) c = (run M n c).bind (run M m) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    simp only [Nat.succ_add, run, Option.bind_assoc, ih]

theorem run_one (M : Program t q a) (c : Config t q a) : run M 1 c = step M c := by
  simp [run]

theorem halted_no_steps (M : Program t q a) (c : Config t q a)
    (h : step M c = none) (k : ℕ) : run M (k + 1) c = none := by
  simp [run, h]

/-- No execution changes a tape cell other than the one under its current head. -/
theorem step_local (M : Program t q a) (c d : Config t q a)
    (h : step M c = some d) (i : Fin t) (j : ℤ) (hj : j ≠ c.head i) :
    d.tape i j = c.tape i j := by
  unfold step at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst d
    simp [hj]

theorem step_head_bound (M : Program t q a) (c d : Config t q a)
    (h : step M c = some d) (i : Fin t) :
    c.head i - 1 ≤ d.head i ∧ d.head i ≤ c.head i + 1 := by
  unfold step at h
  split at h
  · contradiction
  · rename_i result heq
    simp only [Option.some.injEq] at h
    subst d
    have hm := (result i).2.unit
    dsimp
    omega

/-- A real finite transition table: preserve the scanned symbol and move right,
halting at the first blank. -/
def scanRight : Program 1 1 0 where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank then none
    else some (0, fun i => (symbols i, Move.right))

def scanConfig (tape : ℤ → Fin 4) (head : ℤ) : Config 1 1 0 where
  state := 0
  head := fun _ => head
  tape := fun _ => tape

theorem scan_step (f : ℤ → Fin 4) (k : ℤ) (h : f k ≠ blank) :
    step scanRight (scanConfig f k) = some (scanConfig f (k + 1)) := by
  simp only [step, scanRight, scanConfig, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = k
  · subst j
    simp
  · simp [hj]

theorem scan_halt (f : ℤ → Fin 4) (k : ℤ) (h : f k = blank) :
    step scanRight (scanConfig f k) = none := by
  simp [step, scanRight, scanConfig, h]

theorem scan_run (f : ℤ → Fin 4) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f j ≠ blank) :
    run scanRight n (scanConfig f 0) = some (scanConfig f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add, ih (by intro j hj; exact h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one] using scan_step f n (h n (by omega))

/-- The primitive scans exactly `n` cells, preserves the entire tape, and halts
at the next blank. There is no assumed scan-cost interface in this theorem. -/
theorem scan_exact (f : ℤ → Fin 4) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f j ≠ blank) (hend : f n = blank) :
    run scanRight n (scanConfig f 0) = some (scanConfig f n) ∧
    step scanRight (scanConfig f n) = none :=
  ⟨scan_run f n h, scan_halt f n hend⟩

end IntegerMultBounds.Machine
