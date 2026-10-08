import IntegerMultBounds.Machine.PartitionMarked

/-! Literal backwards erasure of a marked stream. Starting at its blank endpoint,
the machine clears each cell through the word origin, retains the sentinel,
steps right, and halts. All cells outside that interval are retained. -/

namespace IntegerMultBounds.Machine.Erase

open PartitionMarked

def program : Program 1 2 1 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 1 then none else
    if symbols 0 = marker then some (1, fun i => (symbols i, .right))
    else some (0, fun _ => (blank, .left))

def cfg (f : ℤ → Fin 5) (p : ℤ) (state : Fin 2) : Config 1 2 1 :=
  ⟨state, fun _ => p, fun _ => f⟩

def cleared (f : ℤ → Fin 5) (lo hi : ℤ) (j : ℤ) : Fin 5 :=
  if lo ≤ j ∧ j ≤ hi then blank else f j

private theorem erase_step (f : ℤ → Fin 5) (p : ℤ) (h : f p ≠ marker) :
    step program (cfg f p 0) = some (cfg (Function.update f p blank) (p - 1) 0) := by
  simp only [step, program, cfg, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  funext i j
  simp [Function.update_apply, eq_comm]

private theorem finish_step (f : ℤ → Fin 5) (p : ℤ) (h : f p = marker) :
    step program (cfg f p 0) = some (cfg f (p + 1) 1) := by
  simp only [step, program, cfg, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp [h]
  · simp [hj]

private theorem erase_scan (f : ℤ → Fin 5) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p - j) ≠ marker) :
    run program n (cfg f p 0) = some (cfg (cleared f (p - n + 1) p) (p - n) 0) := by
  induction n with
  | zero =>
    have he : cleared f (p + 1) p = f := by
      funext j
      have hj : ¬ (p + 1 ≤ j ∧ j ≤ p) := by omega
      simp only [cleared, hj, ↓reduceIte]
    simp only [run, Nat.cast_zero, sub_zero, he]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    have hread : cleared f (p - n + 1) p (p - n) = f (p - n) := by
      simp [cleared]
    rw [erase_step _ _ (by rw [hread]; exact h n (by omega))]
    have he : Function.update (cleared f (p - n + 1) p) (p - n) blank =
        cleared f (p - (n + 1 : ℕ) + 1) p := by
      funext j
      by_cases hj : j = p - n
      · subst j; simp [cleared]
      · have hi : (p - (n + 1 : ℕ) + 1 ≤ j ∧ j ≤ p) ↔ (p - n + 1 ≤ j ∧ j ≤ p) := by omega
        rw [Function.update_of_ne hj]
        simp only [cleared, hi]
    rw [he]
    congr 2
    omega

/-- Writing a marker-free word does not introduce a sentinel at any cell where
the background was not already a sentinel. -/
theorem putWord_ne_marker (f : ℤ → Fin 5) (p j : ℤ) (xs : List (Fin 5))
    (hxs : ∀ x ∈ xs, x ≠ marker) (hf : f j ≠ marker) : putWord f p xs j ≠ marker := by
  induction xs generalizing p with
  | nil => exact hf
  | cons x xs ih =>
    by_cases hj : j = p
    · subst j; rw [putWord_head]; exact hxs x (by simp)
    · rw [putWord, Function.update_of_ne hj]
      exact ih (p + 1) (fun y hy => hxs y (by simp [hy]))

theorem blankMarked_ne_marker (origin j : ℤ) (h : j ≠ origin - 1) :
    markedTape origin [] j ≠ marker := markedTape_ne_marker origin [] j h

private theorem blankMarked_after (origin j : ℤ) (h : origin ≤ j) :
    markedTape origin [] j = blank := by
  have hm : j ≠ origin - 1 := by omega
  simp only [markedTape, hm, ↓reduceIte, putWord]
  rfl

private theorem cleared_word (origin : ℤ) (xs : List (Fin 5)) :
    cleared (putWord (markedTape origin []) origin xs) origin (origin + xs.length) =
      markedTape origin [] := by
  funext j
  by_cases h : origin ≤ j ∧ j ≤ origin + xs.length
  · simp only [cleared, h]
    exact (blankMarked_after origin j h.1).symm
  · simp only [cleared, h]
    apply putWord_outside
    omega

/-- Exact destructive cleanup: endpoint blank plus word plus sentinel crossing.
The resulting whole tape is the original empty marked buffer at its origin. -/
theorem erase_exact (origin : ℤ) (xs : List (Fin 5)) (hxs : ∀ x ∈ xs, x ≠ marker) :
    run program (xs.length + 2)
      (cfg (putWord (markedTape origin []) origin xs) (origin + xs.length) 0) =
      some (cfg (markedTape origin []) origin 1) ∧
    step program (cfg (markedTape origin []) origin 1) = none := by
  have hs := erase_scan (putWord (markedTape origin []) origin xs) (origin + xs.length) (xs.length + 1)
    (by
      intro j hj
      apply putWord_ne_marker _ _ _ _ hxs
      apply blankMarked_ne_marker
      omega)
  have hlo : origin + (xs.length : ℤ) - ((xs.length + 1 : ℕ) : ℤ) + 1 = origin := by omega
  have hhead : origin + (xs.length : ℤ) - ((xs.length + 1 : ℕ) : ℤ) = origin - 1 := by omega
  rw [hlo, hhead, cleared_word] at hs
  have he := finish_step (markedTape origin []) (origin - 1) (markedTape_marker origin [])
  have horigin : origin - 1 + 1 = origin := by omega
  rw [horigin] at he
  refine ⟨?_, ?_⟩
  · change run program ((xs.length + 1) + 1) _ = _
    rw [run_add, hs]
    simpa only [Option.bind_some, run_one] using he
  · simp [step, program, cfg]

theorem erase_hoare (origin : ℤ) (xs : List (Fin 5)) (hxs : ∀ x ∈ xs, x ≠ marker) :
    HoareTime program
      (fun v => v = (cfg (putWord (markedTape origin []) origin xs) (origin + xs.length) 0).tapes)
      (fun v => v = (cfg (markedTape origin []) origin 1).tapes) (xs.length + 2) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := erase_exact origin xs hxs
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.Erase
