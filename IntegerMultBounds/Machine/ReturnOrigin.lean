import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare

/-! Return a head from the end of a blank-backed word to the word's origin:
one step left, then left over every nonblank cell, then one step right from
the blank before the word. One tape, three states, every cell retained, and
exactly the word length plus two transitions. -/

namespace IntegerMultBounds.Machine.ReturnOrigin

variable {a : ℕ}

/-- State zero steps left unconditionally, state one rewinds over nonblank
cells and steps right on the first blank, state two halts. -/
def program : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then
      if symbols 0 = blank then some (2, fun i => (symbols i, .right))
      else some (1, fun i => (symbols i, .left))
    else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 3) : Config 1 3 a := ⟨s, fun _ => p, fun _ => f⟩

private theorem tape_retained (f : ℤ → Fin (a + 4)) (p : ℤ) (x : Fin (a + 4)) (hx : x = f p) :
    (fun (_ : Fin 1) (j : ℤ) => if j = p then x else f j) = fun _ => f := by
  funext i j
  by_cases hj : j = p
  · subst j; simp [hx]
  · simp [hj]

theorem first_step (f : ℤ → Fin (a + 4)) (p : ℤ) :
    step program (cfg f p 0) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ rfl

theorem left_step (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p ≠ blank) :
    step program (cfg f p 1) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ rfl

theorem exit_step (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p = blank) :
    step program (cfg f p 1) = some (cfg f (p + 1) 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ h.symm

theorem halt (f : ℤ → Fin (a + 4)) (p : ℤ) : step program (cfg f p 2) = none := by
  simp [step, program, cfg]

theorem left_run (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p - j) ≠ blank) :
    run program n (cfg f p 1) = some (cfg f (p - n) 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      left_step f (p - n) (h n (by omega))

/-- Every cell of a placed word is one of its symbols. -/
theorem putWord_mem (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (j : ℤ)
    (hj : p ≤ j ∧ j < p + xs.length) : putWord f p xs j ∈ xs := by
  induction xs generalizing p with
  | nil => simp only [List.length_nil, Nat.cast_zero, add_zero] at hj; omega
  | cons x xs ih =>
    simp only [putWord, Function.update_apply]
    by_cases hx : j = p
    · simp [hx]
    · simp only [hx, ↓reduceIte, List.mem_cons]
      exact Or.inr (ih (p + 1) (by simp only [List.length_cons] at hj; omega))

/-- From the end of a blank-backed nonblank word, return to its origin in the
word length plus two transitions, retaining the whole tape. -/
theorem return_exact (xs : List (Fin (a + 4))) (hx : ∀ x ∈ xs, x ≠ blank) :
    run program (xs.length + 2) (cfg (putWord (fun _ => blank) 0 xs) xs.length 0) =
      some (cfg (putWord (fun _ => blank) 0 xs) 0 2) ∧
    step program (cfg (putWord (fun _ => blank) 0 xs) 0 2) = none := by
  refine ⟨?_, halt _ _⟩
  have hl := left_run (putWord (fun _ => blank) 0 xs) ((xs.length : ℤ) - 1) xs.length (by
    intro j hj
    exact hx _ (putWord_mem _ _ _ _ ⟨by omega, by omega⟩))
  have hout : putWord (fun _ => blank) 0 xs ((xs.length : ℤ) - 1 - xs.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inl (by omega))]
  have he := exit_step (putWord (fun _ => blank) 0 xs) _ hout
  rw [show xs.length + 2 = 1 + xs.length + 1 by omega, run_add, run_add, run_one, first_step]
  simp only [Option.bind_some, hl, run_one, he]
  congr 2
  omega

theorem return_hoare (xs : List (Fin (a + 4))) (hx : ∀ x ∈ xs, x ≠ blank) :
    HoareTime program
      (fun v => v = (cfg (putWord (fun _ => blank) 0 xs) xs.length 0).tapes)
      (fun v => v = (cfg (putWord (fun _ => blank) 0 xs) 0 2).tapes)
      (xs.length + 2) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := return_exact xs hx
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.ReturnOrigin
