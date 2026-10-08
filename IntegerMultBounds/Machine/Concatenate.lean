import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare

/-! A literal three-tape, two-state concatenation machine. Tape zero is copied
first, then tape one, into tape two. The one-step phase switch preserves every
head and cell. Sources are blank-terminated; no markers or rewinds are needed. -/

namespace IntegerMultBounds.Machine.Concatenate

variable {a : ℕ}

/-- Copy the two source tapes consecutively, preserving their complete contents. -/
def program : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun phase symbols =>
    let source : Fin 3 := if phase = 0 then 0 else 1
    if symbols source = blank then
      if phase = 0 then some (1, fun i => (symbols i, .stay)) else none
    else some (phase, fun i =>
      if i = 2 then (symbols source, .right)
      else (symbols i, if i = source then .right else .stay))

def cfg (phase : Fin 2) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) : Config 3 2 a where
  state := phase
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

theorem left_step (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (h : f p ≠ blank) :
    step program (cfg 0 f g out p q r) =
      some (cfg 0 f g (Function.update out r (f p)) (p + 1) q (r + 1)) := by
  simp only [step, program, cfg, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

theorem right_step (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (h : g q ≠ blank) :
    step program (cfg 1 f g out p q r) =
      some (cfg 1 f g (Function.update out r (g q)) p (q + 1) (r + 1)) := by
  simp only [step, program, cfg, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    show (1 : Fin 3) ≠ 0 by decide, h, Move.offset]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

/-- Encountering the first terminator consumes exactly one transition. -/
theorem switch_step (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (h : f p = blank) :
    step program (cfg 0 f g out p q r) = some (cfg 1 f g out p q r) := by
  simp only [step, program, cfg, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp <;> intro hj <;> rw [hj]

theorem halt (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (h : g q = blank) :
    step program (cfg 1 f g out p q r) = none := by
  simp [step, program, cfg, h]

/-- Exact first phase, including preservation of both whole source tapes. -/
theorem left_run (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (xs : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ blank) :
    run program xs.length (cfg 0 (putWord f p xs) g out p q r) =
      some (cfg 0 (putWord f p xs) g (putWord out r xs) (p + xs.length) q
        (r + xs.length)) := by
  induction xs generalizing f out p r with
  | nil => simp [putWord, run]
  | cons x xs ih =>
    have hs := left_step (putWord f p (x :: xs)) g out p q r
      (by rw [putWord_head]; exact hxs x (by simp))
    rw [putWord_head] at hs
    simp only [List.length_cons, run, hs, Option.bind_some]
    rw [putWord_cons]
    have hr := ih (Function.update f p x) (Function.update out r x) (p + 1) (r + 1)
      (fun y hy => hxs y (by simp [hy]))
    simpa only [← putWord_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Exact second phase, with the first source head held fixed. -/
theorem right_run (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (ys : List (Fin (a + 4))) (hys : ∀ y ∈ ys, y ≠ blank) :
    run program ys.length (cfg 1 f (putWord g q ys) out p q r) =
      some (cfg 1 f (putWord g q ys) (putWord out r ys) p (q + ys.length)
        (r + ys.length)) := by
  induction ys generalizing g out q r with
  | nil => simp [putWord, run]
  | cons y ys ih =>
    have hs := right_step f (putWord g q (y :: ys)) out p q r
      (by rw [putWord_head]; exact hys y (by simp))
    rw [putWord_head] at hs
    simp only [List.length_cons, run, hs, Option.bind_some]
    rw [putWord_cons]
    have hr := ih (Function.update g q y) (Function.update out r y) (q + 1) (r + 1)
      (fun z hz => hys z (by simp [hz]))
    simpa only [← putWord_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- The entire run uses one transition per copied symbol and one phase switch.
The output contract specifies all cells, including arbitrary untouched background. -/
theorem concatenate_run (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (xs ys : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ blank)
    (hys : ∀ y ∈ ys, y ≠ blank) (hxend : f (p + xs.length) = blank) :
    run program (xs.length + 1 + ys.length)
      (cfg 0 (putWord f p xs) (putWord g q ys) out p q r) =
      some (cfg 1 (putWord f p xs) (putWord g q ys) (putWord out r (xs ++ ys))
        (p + xs.length) (q + ys.length) (r + (xs ++ ys).length)) := by
  rw [run_add, run_add, left_run _ _ _ _ _ _ xs hxs]
  simp only [Option.bind_some, run_one]
  rw [switch_step _ _ _ _ _ _ (by rw [putWord_outside _ _ _ _ (Or.inr (by omega))]; exact hxend)]
  simp only [Option.bind_some]
  rw [right_run _ _ _ _ _ _ ys hys, putWord_append_forward]
  simp [List.length_append, Nat.cast_add, add_assoc]

theorem concatenate_exact (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (xs ys : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ blank)
    (hys : ∀ y ∈ ys, y ≠ blank) (hxend : f (p + xs.length) = blank)
    (hyend : g (q + ys.length) = blank) :
    run program (xs.length + 1 + ys.length)
      (cfg 0 (putWord f p xs) (putWord g q ys) out p q r) =
      some (cfg 1 (putWord f p xs) (putWord g q ys) (putWord out r (xs ++ ys))
        (p + xs.length) (q + ys.length) (r + (xs ++ ys).length)) ∧
    step program (cfg 1 (putWord f p xs) (putWord g q ys) (putWord out r (xs ++ ys))
      (p + xs.length) (q + ys.length) (r + (xs ++ ys).length)) = none := by
  refine ⟨concatenate_run f g out p q r xs ys hxs hys hxend, halt _ _ _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr (by omega)), hyend]

def tapes (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) : Tapes 3 a :=
  (cfg 0 f g out p q r).tapes

/-- A whole-tape time contract, with both source heads at the initial word starts. -/
theorem concatenate_hoare (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (xs ys : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ blank)
    (hys : ∀ y ∈ ys, y ≠ blank) (hxend : f (p + xs.length) = blank)
    (hyend : g (q + ys.length) = blank) :
    HoareTime program
      (fun v => v = tapes (putWord f p xs) (putWord g q ys) out p q r)
      (fun v => v = tapes (putWord f p xs) (putWord g q ys) (putWord out r (xs ++ ys))
        (p + xs.length) (q + ys.length) (r + (xs ++ ys).length))
      (xs.length + 1 + ys.length) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := concatenate_exact f g out p q r xs ys hxs hys hxend hyend
  exact ⟨xs.length + 1 + ys.length, _, le_rfl, hr, hh, rfl⟩

/-- A blank output background gives precisely the concatenated word at the
chosen output origin and blanks everywhere else, not merely a trailing blank. -/
theorem concatenate_to_blank (f g : ℤ → Fin (a + 4)) (p q r : ℤ)
    (xs ys : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ blank)
    (hys : ∀ y ∈ ys, y ≠ blank) (hxend : f (p + xs.length) = blank)
    (hyend : g (q + ys.length) = blank) :
    run program (xs.length + 1 + ys.length)
      (cfg 0 (putWord f p xs) (putWord g q ys) (fun _ => blank) p q r) =
      some (cfg 1 (putWord f p xs) (putWord g q ys)
        (fun j => wordTape (xs ++ ys) (j - r))
        (p + xs.length) (q + ys.length) (r + (xs ++ ys).length)) ∧
    step program (cfg 1 (putWord f p xs) (putWord g q ys)
      (fun j => wordTape (xs ++ ys) (j - r))
      (p + xs.length) (q + ys.length) (r + (xs ++ ys).length)) = none := by
  have hw : putWord (fun _ => blank) r (xs ++ ys) =
      fun j => wordTape (xs ++ ys) (j - r) := by
    funext j
    exact putWord_blank r j (xs ++ ys)
  simpa only [hw] using concatenate_exact f g (fun _ => blank) p q r xs ys hxs hys hxend hyend

end IntegerMultBounds.Machine.Concatenate

