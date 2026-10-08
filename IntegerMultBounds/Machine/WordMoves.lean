import IntegerMultBounds.Machine.ExactFrame

/-! Small word-moving routines on blank-terminated words, for any alphabet:
scan to a word's end, copy a word onto another tape, erase a word backwards
to its origin, and copy a fixed number of cells with blanks read as zero
bits. Each has an exact contract with its transition count. -/

namespace IntegerMultBounds.Machine

variable {a : ℕ}

/-- Blank cells outside a word's background may be absorbed into the word. -/
theorem putWord_replicate_blank (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p + j) = blank) :
    putWord f p (List.replicate n blank) = f := by
  induction n generalizing f p with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, putWord_cons, ih (Function.update f p blank) (p + 1) (fun j hj => by
      rw [Function.update_of_ne (by omega), show p + 1 + (j : ℤ) = p + ((j + 1 : ℕ) : ℤ) by push_cast; ring]
      exact h (j + 1) (by omega))]
    funext j
    by_cases hj : j = p
    · subst j; simpa using (h 0 (by omega)).symm
    · simp [hj]

namespace ScanEnd

/-- Step right over nonblank cells; halt on the first blank. -/
def program : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank then none else some (0, fun i => (symbols i, .right))

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) : Config 1 1 a := ⟨0, fun _ => p, fun _ => f⟩

theorem scan_step (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p ≠ blank) :
    step program (cfg f p) = some (cfg f (p + 1)) := by
  simp only [step, program, cfg, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem scan_run (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p + j) ≠ blank) :
    run program n (cfg f p) = some (cfg f (p + n)) := by
  induction n generalizing p with
  | zero => simp [run]
  | succ n ih =>
    rw [add_comm, run_add, run_one, scan_step f p (by simpa using h 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (p + 1) (fun j hj => by
      rw [show p + 1 + (j : ℤ) = p + ((j + 1 : ℕ) : ℤ) by push_cast; ring]
      exact h (j + 1) (by omega))]
    congr 2
    push_cast; ring

theorem scan_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hend : f (p + xs.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) p).tapes)
      (fun v => v = (cfg (putWord f p xs) (p + xs.length)).tapes) xs.length := by
  rintro v rfl
  refine ⟨xs.length, cfg (putWord f p xs) (p + xs.length), le_rfl, ?_, ?_, rfl⟩
  · exact scan_run (putWord f p xs) p xs.length (fun j hj =>
      hx _ (ReturnOrigin.putWord_mem f p xs (p + j) ⟨by omega, by omega⟩))
  · simp [step, program, cfg, putWord_outside _ _ _ _ (Or.inr (le_refl _)), hend]

end ScanEnd

namespace CopyWord

/-- Copy the nonblank word under the first head onto the second tape, both
heads advancing; halt on the source blank. -/
def program : Program 2 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank then none
    else some (0, fun i => (symbols 0, .right))

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) : Config 2 1 a :=
  ⟨0, fun i => if i = 0 then p else q, fun i => if i = 0 then f else g⟩

theorem copy_step (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p ≠ blank) :
    step program (cfg f g p q) = some (cfg f (Function.update g q (f p)) (p + 1) (q + 1)) := by
  simp only [step, program, cfg, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

theorem copy_run (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) :
    run program xs.length (cfg (putWord f p xs) g p q) =
      some (cfg (putWord f p xs) (putWord g q xs) (p + xs.length) (q + xs.length)) := by
  induction xs generalizing f g p q with
  | nil => simp [run, putWord]
  | cons x xs ih =>
    rw [List.length_cons, add_comm, run_add, run_one,
      copy_step _ _ _ _ (by rw [putWord_head]; exact hx x (by simp))]
    simp only [Option.bind_some, putWord_head, putWord_cons]
    rw [ih (Function.update f p x) (Function.update g q x) (p + 1) (q + 1)
      (fun y hy => hx y (by simp [hy]))]
    congr 2 <;> push_cast <;> ring

theorem copy_hoare (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hend : f (p + xs.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) g p q).tapes)
      (fun v => v = (cfg (putWord f p xs) (putWord g q xs) (p + xs.length) (q + xs.length)).tapes)
      xs.length := by
  rintro v rfl
  refine ⟨xs.length, _, le_rfl, copy_run f g p q xs hx, ?_, rfl⟩
  simp [step, program, cfg, putWord_outside _ _ _ _ (Or.inr (le_refl _)), hend]

end CopyWord

namespace EraseBack

/-- From the blank after a word, erase it leftwards and stop on its origin. -/
def program : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then
      if symbols 0 = blank then some (2, fun i => (symbols i, .right))
      else some (1, fun _ => (blank, .left))
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

theorem erase_step (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p ≠ blank) :
    step program (cfg f p 1) = some (cfg (Function.update f p blank) (p - 1) 1) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem exit_step (f : ℤ → Fin (a + 4)) (p : ℤ) (h : f p = blank) :
    step program (cfg f p 1) = some (cfg f (p + 1) 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp [h]
  · simp [hj]

/-- The tape with the cells of a range blanked. -/
def eraseRange (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ) : ℤ → Fin (a + 4) :=
  fun j => if p ≤ j ∧ j < p + n then blank else f j

theorem eraseRange_zero (f : ℤ → Fin (a + 4)) (p : ℤ) : eraseRange f p 0 = f := by
  funext j; simp [eraseRange]

theorem eraseRange_succ (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ) :
    eraseRange (Function.update f (p + n) blank) p n = eraseRange f p (n + 1) := by
  funext j
  simp only [eraseRange, Function.update_apply]
  push_cast
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Erasing a word whose background is blank restores the background. -/
theorem eraseRange_putWord (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hf : ∀ j : ℕ, j < xs.length → f (p + j) = blank) :
    eraseRange (putWord f p xs) p xs.length = f := by
  funext j
  simp only [eraseRange]
  split_ifs with h
  · obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < xs.length ∧ j = p + k :=
      ⟨(j - p).toNat, by omega, by omega⟩
    exact (hf k hk).symm
  · exact putWord_outside _ _ _ _ (by omega)

/-- Erasing cells from the right end backwards, one transition per cell. -/
theorem erase_run (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ) (h : ∀ j : ℕ, j < n → f (p + j) ≠ blank) :
    run program n (cfg f (p + n - 1) 1) = some (cfg (eraseRange f p n) (p - 1) 1) := by
  induction n generalizing f with
  | zero => simp [run, eraseRange_zero]
  | succ n ih =>
    simp only [run]
    rw [show p + ((n + 1 : ℕ) : ℤ) - 1 = p + n by push_cast; ring, erase_step f (p + n) (h n (by omega))]
    simp only [Option.bind_some]
    rw [show p + (n : ℤ) - 1 = p + n - 1 by ring, ih (Function.update f (p + n) blank) (fun j hj => by
      rw [Function.update_of_ne (by omega)]; exact h j (by omega)), eraseRange_succ]

/-- From the blank after a word over a blank background, erase the word and
stop on its origin; the word length plus two transitions. -/
theorem erase_hoare (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4)))
    (hx : ∀ x ∈ xs, x ≠ blank) (hleft : f (p - 1) = blank)
    (hf : ∀ j : ℕ, j < xs.length → f (p + j) = blank) :
    HoareTime program (fun v => v = (cfg (putWord f p xs) (p + xs.length) 0).tapes)
      (fun v => v = (cfg f p 2).tapes) (xs.length + 2) := by
  rintro v rfl
  refine ⟨xs.length + 2, cfg f p 2, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  have h0 : (cfg (putWord f p xs) (p + xs.length) 0).tapes.start program =
      cfg (putWord f p xs) (p + xs.length) 0 := rfl
  rw [h0, show xs.length + 2 = 1 + xs.length + 1 by omega, run_add, run_add, run_one, first_step]
  simp only [Option.bind_some]
  rw [erase_run (putWord f p xs) p xs.length (fun j hj =>
    hx _ (ReturnOrigin.putWord_mem f p xs (p + j) ⟨by omega, by omega⟩)), eraseRange_putWord f p xs hf]
  simp only [Option.bind_some, run_one]
  rw [exit_step f (p - 1) hleft]
  congr 2
  ring

end EraseBack

namespace CopyCells

/-- A blank reads as a zero bit. -/
def zeroFill (x : Fin (a + 4)) : Fin (a + 4) := if x = blank then bitSymbol false else x

/-- Copy one cell, zero-filled, and advance both heads. -/
def cell : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (if i = 1 then zeroFill (symbols 0) else symbols i, .right))
    else none

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) (s : Fin 2) : Config 2 2 a :=
  ⟨s, fun i => if i = 0 then p else q, fun i => if i = 0 then f else g⟩

theorem cell_hoare (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    HoareTime cell (fun v => v = (cfg f g p q 0).tapes)
      (fun v => v = (cfg f (Function.update g q (zeroFill (f p))) (p + 1) (q + 1) 0).tapes) 1 := by
  rintro v rfl
  refine ⟨1, cfg f (Function.update g q (zeroFill (f p))) (p + 1) (q + 1) 1, le_rfl, ?_,
    by simp [step, cell, cfg], rfl⟩
  rw [run_one]
  simp only [step, cell, cfg, Tapes.start, Config.tapes, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

/-- The state count of the unrolled copier. -/
def states : ℕ → ℕ
  | 0 => 1
  | c + 1 => 2 + states c

/-- Copy exactly `c` cells, zero-filled. -/
def program : (c : ℕ) → Program 2 (states c) a
  | 0 => skip 2 a (by decide)
  | c + 1 => seq cell (program c)

/-- The copied cells. -/
def cells (f : ℤ → Fin (a + 4)) (p : ℤ) : ℕ → List (Fin (a + 4))
  | 0 => []
  | c + 1 => zeroFill (f p) :: cells f (p + 1) c

theorem cells_length (f : ℤ → Fin (a + 4)) (p : ℤ) (c : ℕ) : (cells f p c).length = c := by
  induction c generalizing p with
  | zero => rfl
  | succ c ih => simp [cells, ih]

/-- The cost: one transition per cell plus one join per cell. -/
def cost : ℕ → ℕ
  | 0 => 0
  | c + 1 => 1 + 1 + cost c

theorem cost_eq (c : ℕ) : cost c = 2 * c := by
  induction c with
  | zero => rfl
  | succ c ih => simp [cost, ih]; ring

theorem copy_hoare (c : ℕ) (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    HoareTime (program c) (fun v => v = (cfg f g p q 0).tapes)
      (fun v => v = (cfg f (putWord g q (cells f p c)) (p + c) (q + c) 0).tapes) (cost c) := by
  induction c generalizing g p q with
  | zero =>
    exact (skip_hoare _ _).consequence (fun v hv => hv) (fun v hv => by
      rw [hv]; simp [cells, putWord]) le_rfl
  | succ c ih =>
    refine ((cell_hoare f g p q).seq (ih (Function.update g q (zeroFill (f p))) (p + 1) (q + 1))).consequence
      (fun v hv => hv) (fun v hv => ?_) le_rfl
    rw [hv, cells, putWord_cons]
    congr 2 <;> push_cast <;> ring

/-- Copying the cells of a placed bit word reproduces the word. -/
theorem cells_putWord (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List Bool) :
    cells (putWord f p (xs.map bitSymbol)) p xs.length = xs.map bitSymbol := by
  induction xs generalizing f p with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.length_cons, cells, putWord_head, putWord_cons, ih]
    cases x <;> simp [zeroFill, bitSymbol, blank]

/-- Copying blank cells yields zero bits. -/
theorem cells_blank (p : ℤ) (c : ℕ) :
    cells (fun _ => (blank : Fin (a + 4))) p c = List.replicate c (bitSymbol false) := by
  induction c generalizing p with
  | zero => rfl
  | succ c ih => simp [cells, ih, zeroFill, List.replicate_succ]

end CopyCells

end IntegerMultBounds.Machine
