import IntegerMultBounds.Machine.ReturnOrigin
import IntegerMultBounds.Machine.PartitionMarked
import IntegerMultBounds.Machine.DropFlag

/-! Return a head from the end of a written word to the word's origin, over
either a blank or a marked background: one step left, then left over every
cell that is neither blank nor the marker, then one step right. One tape,
three states, every cell retained, exactly the word length plus two
transitions. -/

namespace IntegerMultBounds.Machine.MarkedReturn

open PartitionMarked (marker markedTape)

/-- A boundary cell: blank or the marker. -/
def boundary (x : Fin 5) : Bool := x = blank || x = marker

/-- State zero steps left unconditionally, state one rewinds over interior
cells and steps right on the first boundary cell, state two halts. -/
def program : Program 1 3 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1, fun i => (symbols i, .left))
    else if s = 1 then
      if boundary (symbols 0) then some (2, fun i => (symbols i, .right))
      else some (1, fun i => (symbols i, .left))
    else none

def cfg (f : ℤ → Fin 5) (p : ℤ) (s : Fin 3) : Config 1 3 1 := ⟨s, fun _ => p, fun _ => f⟩

private theorem tape_retained (f : ℤ → Fin 5) (p : ℤ) (x : Fin 5) (hx : x = f p) :
    (fun (_ : Fin 1) (j : ℤ) => if j = p then x else f j) = fun _ => f := by
  funext i j
  by_cases hj : j = p
  · subst j; simp [hx]
  · simp [hj]

theorem first_step (f : ℤ → Fin 5) (p : ℤ) :
    step program (cfg f p 0) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ rfl

theorem left_step (f : ℤ → Fin 5) (p : ℤ) (h : boundary (f p) = false) :
    step program (cfg f p 1) = some (cfg f (p - 1) 1) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h,
    Bool.false_eq_true, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ rfl

theorem exit_step (f : ℤ → Fin 5) (p : ℤ) (h : boundary (f p) = true) :
    step program (cfg f p 1) = some (cfg f (p + 1) 2) := by
  simp only [step, program, cfg, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  exact tape_retained f p _ rfl

theorem halt (f : ℤ → Fin 5) (p : ℤ) : step program (cfg f p 2) = none := by
  simp [step, program, cfg]

theorem left_run (f : ℤ → Fin 5) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → boundary (f (p - j)) = false) :
    run program n (cfg f p 1) = some (cfg f (p - n) 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      left_step f (p - n) (h n (by omega))

theorem boundary_false (x : Fin 5) (hb : x ≠ blank) (hm : x ≠ marker) : boundary x = false := by
  simp [boundary, hb, hm]

/-- From the end of a word of interior symbols whose left neighbour is a
boundary cell, return to the origin in the word length plus two transitions. -/
theorem return_exact (f : ℤ → Fin 5) (p : ℤ) (xs : List (Fin 5))
    (hx : ∀ x ∈ xs, x ≠ blank ∧ x ≠ marker) (hleft : boundary (f (p - 1)) = true) :
    run program (xs.length + 2) (cfg (putWord f p xs) (p + xs.length) 0) =
      some (cfg (putWord f p xs) p 2) ∧
    step program (cfg (putWord f p xs) p 2) = none := by
  refine ⟨?_, halt _ _⟩
  have hl := left_run (putWord f p xs) (p + xs.length - 1) xs.length (by
    intro j hj
    have hmem := ReturnOrigin.putWord_mem f p xs (p + xs.length - 1 - j) ⟨by omega, by omega⟩
    exact boundary_false _ (hx _ hmem).1 (hx _ hmem).2)
  have hout : boundary (putWord f p xs (p + xs.length - 1 - xs.length)) = true := by
    rw [putWord_outside _ _ _ _ (Or.inl (by omega)), show p + (xs.length : ℤ) - 1 - xs.length = p - 1
      by ring]
    exact hleft
  have he := exit_step (putWord f p xs) _ hout
  rw [show xs.length + 2 = 1 + xs.length + 1 by omega, run_add, run_add, run_one, first_step]
  simp only [Option.bind_some, hl, run_one, he]
  congr 2
  ring

theorem return_hoare (f : ℤ → Fin 5) (p : ℤ) (xs : List (Fin 5))
    (hx : ∀ x ∈ xs, x ≠ blank ∧ x ≠ marker) (hleft : boundary (f (p - 1)) = true) :
    HoareTime program
      (fun v => v = (cfg (putWord f p xs) (p + xs.length) 0).tapes)
      (fun v => v = (cfg (putWord f p xs) p 2).tapes)
      (xs.length + 2) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := return_exact f p xs hx hleft
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

/-- Raw keyed records and widened flagged records are interior words. -/
theorem keySelect_interior (records : List (List Bool)) :
    ∀ x ∈ KeySelect.encode records, x ≠ blank ∧ x ≠ marker := by
  induction records with
  | nil => simp [KeySelect.encode]
  | cons bits rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · refine ⟨KeySelect.recordWord_nonblank bits x hx, ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
        cases b <;> decide
      · simp only [List.mem_singleton] at hx
        subst x
        decide
    · exact ih x hx

theorem dropFlag_interior (records : List Partition.Record) :
    ∀ x ∈ DropFlag.encode records, x ≠ blank ∧ x ≠ marker := by
  induction records with
  | nil => simp [DropFlag.encode]
  | cons rec rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [DropFlag.recordWord, List.mem_cons] at hx
      rcases hx with rfl | hx
      · cases rec.key <;> decide
      · exact keySelect_interior [rec.payload] x (by simpa [KeySelect.encode] using hx)
    · exact ih x hx

end IntegerMultBounds.Machine.MarkedReturn
