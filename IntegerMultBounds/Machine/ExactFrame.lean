import IntegerMultBounds.Machine.Frame
import IntegerMultBounds.Machine.ReturnOrigin

/-! Exact-tape forms of the frame rules, for any alphabet: a contract between
two fully specified banks lifts to an extended or relabelled bank. Also the
rewind to a word's origin from an arbitrary position with an arbitrary
background, and two one-tape moves used when assembling arithmetic. -/

namespace IntegerMultBounds.Machine

variable {t s u q a : ℕ}

theorem hoare_extend_eq {M : Program t q a} {X X' : Tapes t a} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) (extra : Tapes s a) :
    HoareTime (extend M s) (fun v => v = X.append extra) (fun v => v = X'.append extra) b :=
  (h.extend extra).consequence (fun v hv => ⟨X, rfl, hv⟩)
    (fun v ⟨small, hs, hv⟩ => by rw [hv, hs]) le_rfl

theorem hoare_reindex_eq {M : Program t q a} {X X' : Tapes t a} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) (e : Fin t ≃ Fin u) :
    HoareTime (reindex M e) (fun v => v = X.reindex e) (fun v => v = X'.reindex e) b :=
  (h.reindex e).consequence (fun v hv => ⟨X, rfl, hv⟩)
    (fun v ⟨orig, ho, hv⟩ => by rw [hv, ho]) le_rfl

theorem hoare_place {M : Program t q a} {X X' : Tapes t a} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) (e : Fin (t + s) ≃ Fin u)
    (extra : Tapes s a) :
    HoareTime (reindex (extend M s) e) (fun v => v = (X.append extra).reindex e)
      (fun v => v = (X'.append extra).reindex e) b :=
  hoare_reindex_eq (hoare_extend_eq h extra) e

/-- A program that halts at once, for the empty branch of a conditional. -/
def skip (t a : ℕ) (ht : 0 < t) : Program t 1 a where
  tapes_pos := ht
  start := 0
  transition := fun _ _ => none

theorem skip_hoare (ht : 0 < t) (X : Tapes t a) :
    HoareTime (skip t a ht) (fun v => v = X) (fun v => v = X) 0 :=
  fun v hv => ⟨0, v.start (skip t a ht), le_rfl, rfl, by simp [step, skip], hv⟩

namespace ReturnOrigin

/-- From the end of a nonblank word whose left neighbour is blank, return to
the word's origin, with an arbitrary background elsewhere. -/
theorem return_exact_at (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hleft : f (p - 1) = blank) :
    run program (xs.length + 2) (cfg (putWord f p xs) (p + xs.length) 0) =
      some (cfg (putWord f p xs) p 2) ∧
    step program (cfg (putWord f p xs) p 2) = none := by
  refine ⟨?_, halt _ _⟩
  have hl := left_run (putWord f p xs) (p + xs.length - 1) xs.length (by
    intro j hj
    exact hx _ (putWord_mem f p xs (p + xs.length - 1 - j) ⟨by omega, by omega⟩))
  have hout : putWord f p xs (p + xs.length - 1 - xs.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inl (by omega)),
      show p + (xs.length : ℤ) - 1 - xs.length = p - 1 by ring]
    exact hleft
  have he := exit_step (putWord f p xs) _ hout
  rw [show xs.length + 2 = 1 + xs.length + 1 by omega, run_add, run_add, run_one, first_step]
  simp only [Option.bind_some, hl, run_one, he]
  congr 2
  omega

theorem return_hoare_at (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hleft : f (p - 1) = blank) :
    HoareTime program
      (fun v => v = (cfg (putWord f p xs) (p + xs.length) 0).tapes)
      (fun v => v = (cfg (putWord f p xs) p 2).tapes)
      (xs.length + 2) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := return_exact_at f p xs hx hleft
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

theorem bits_nonblank (bs : List Bool) : ∀ x ∈ bs.map (bitSymbol (a := a)), x ≠ blank := by
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  cases b <;> simp [bitSymbol, blank]

end ReturnOrigin

namespace StepLeft

/-- One step left on a single tape, retaining every cell. -/
def program : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left)) else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 2) : Config 1 2 a := ⟨s, fun _ => p, fun _ => f⟩

theorem step_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) :
    HoareTime program (fun v => v = (cfg f p 0).tapes) (fun v => v = (cfg f (p - 1) 0).tapes) 1 := by
  rintro v rfl
  refine ⟨1, cfg f (p - 1) 1, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  rw [run_one]
  simp only [step, program, cfg, Tapes.start, Config.tapes, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

end StepLeft

namespace PrependZero

/-- Step left and write a zero bit there: the word starting one cell to the
right is doubled in least-significant-first reading. -/
def program : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then some (2, fun _ => (bitSymbol false, .stay))
    else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 3) : Config 1 3 a := ⟨s, fun _ => p, fun _ => f⟩

theorem first_step (f : ℤ → Fin (a + 4)) (p : ℤ) :
    step program (cfg f p 0) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem write_step (f : ℤ → Fin (a + 4)) (p : ℤ) :
    step program (cfg f p 1) = some (cfg (Function.update f p (bitSymbol false)) p 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; simp
  · funext i j
    by_cases hj : j = p
    · subst j; simp
    · simp [hj]

theorem prepend_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) :
    HoareTime program (fun v => v = (cfg f p 0).tapes)
      (fun v => v = (cfg (Function.update f (p - 1) (bitSymbol false)) (p - 1) 0).tapes) 2 := by
  rintro v rfl
  refine ⟨2, cfg (Function.update f (p - 1) (bitSymbol false)) (p - 1) 2, le_rfl, ?_,
    by simp [step, program, cfg], rfl⟩
  have h0 : (cfg f p 0).tapes.start program = cfg f p 0 := rfl
  rw [h0, run_add program 1 1, run_one, first_step]
  simp only [Option.bind_some, run_one, write_step]

/-- Prepending a symbol to a placed word. -/
theorem putWord_prepend_symbol (f : ℤ → Fin (a + 4)) (p : ℤ) (x : Fin (a + 4))
    (xs : List (Fin (a + 4))) :
    Function.update (putWord f p xs) (p - 1) x = putWord f (p - 1) (x :: xs) := by
  rw [putWord_cons, putWord_update_before _ _ _ _ _ (by omega)]
  congr 1
  simp

/-- Prepending a zero to a placed word. -/
theorem putWord_prepend (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) :
    Function.update (putWord f p xs) (p - 1) (bitSymbol false) =
      putWord f (p - 1) (bitSymbol false :: xs) :=
  putWord_prepend_symbol f p _ xs

end PrependZero

namespace EraseCell

/-- Blank the scanned cell of a single tape without moving. -/
def program : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ =>
    if s = 0 then some (1, fun _ => (blank, .stay)) else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 2) : Config 1 2 a := ⟨s, fun _ => p, fun _ => f⟩

theorem erase_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) :
    HoareTime program (fun v => v = (cfg f p 0).tapes)
      (fun v => v = (cfg (Function.update f p blank) p 0).tapes) 1 := by
  rintro v rfl
  refine ⟨1, cfg (Function.update f p blank) p 1, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  rw [run_one]
  simp only [step, program, cfg, Tapes.start, Config.tapes, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; simp
  · funext i j
    by_cases hj : j = p
    · subst j; simp
    · simp [hj]

/-- Erasing the single written cell of a word of length one restores the
blank background. -/
theorem erase_single (p : ℤ) (x : Fin (a + 4)) :
    Function.update (putWord (fun _ => blank) p [x]) p blank = fun _ => blank := by
  funext j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj, putWord]

end EraseCell

end IntegerMultBounds.Machine
