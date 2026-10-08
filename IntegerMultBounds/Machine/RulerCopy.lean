import IntegerMultBounds.Machine.RulerAdvance

/-! Copy as many cells as a ruler word is long, zero-filled, from a source
head to a destination head: three tapes and one state, all heads stepping
right together while the ruler reads nonblank. Also a one-cell writer of a
fixed symbol. -/

namespace IntegerMultBounds.Machine.RulerCopy

open CopyCells (zeroFill cells)

variable {a : ℕ}

def program : Program 3 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank then none
    else some (0, fun i => if i = 2 then (zeroFill (symbols 1), .right) else (symbols i, .right))

def cfg (r f g : ℤ → Fin (a + 4)) (pr p q : ℤ) : Config 3 1 a :=
  ⟨0, fun i => if i = 0 then pr else if i = 1 then p else q,
   fun i => if i = 0 then r else if i = 1 then f else g⟩

theorem copy_step (r f g : ℤ → Fin (a + 4)) (pr p q : ℤ) (h : r pr ≠ blank) :
    step program (cfg r f g pr p q) =
      some (cfg r f (Function.update g q (zeroFill (f p))) (pr + 1) (p + 1) (q + 1)) := by
  unfold step
  simp only [cfg, program, h, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (try (intro hj; rw [hj]))

theorem copy_run (r f g : ℤ → Fin (a + 4)) (pr p q : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → r (pr + j) ≠ blank) :
    run program n (cfg r f g pr p q) =
      some (cfg r f (putWord g q (cells f p n)) (pr + n) (p + n) (q + n)) := by
  induction n generalizing pr p q g with
  | zero => simp [run, cells, putWord]
  | succ n ih =>
    rw [run, copy_step _ _ _ _ _ _ (by simpa using h 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (Function.update g q (zeroFill (f p))) (pr + 1) (p + 1) (q + 1) (fun j hj => by
      rw [show pr + 1 + (j : ℤ) = pr + ((j + 1 : ℕ) : ℤ) by push_cast; ring]
      exact h (j + 1) (by omega))]
    rw [cells, putWord_cons]
    congr 2 <;> push_cast <;> ring

/-- The exact contract: the destination receives the zero-filled cells under
the source, all three heads advance by the ruler's length, and the ruler head
parks on its blank end. -/
theorem copy_hoare (r f g : ℤ → Fin (a + 4)) (pr p q : ℤ) (rs : List (Fin (a + 4)))
    (hx : ∀ x ∈ rs, x ≠ blank) (hend : r (pr + rs.length) = blank) :
    HoareTime program (fun v => v = (cfg (putWord r pr rs) f g pr p q).tapes)
      (fun v => v = (cfg (putWord r pr rs) f (putWord g q (cells f p rs.length))
        (pr + rs.length) (p + rs.length) (q + rs.length)).tapes) rs.length := by
  rintro v rfl
  refine ⟨rs.length, _, le_rfl, ?_, ?_, rfl⟩
  · exact copy_run (putWord r pr rs) f g pr p q rs.length (fun j hj =>
      hx _ (ReturnOrigin.putWord_mem r pr rs (pr + j) ⟨by omega, by omega⟩))
  · simp [step, program, cfg, putWord_outside _ _ _ _ (Or.inr (le_refl _)), hend]

end IntegerMultBounds.Machine.RulerCopy

namespace IntegerMultBounds.Machine.WriteSymbol

variable {a : ℕ}

/-- Write a fixed symbol without moving. -/
def program (x : Fin (a + 4)) : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ =>
    if s = 0 then some (1, fun _ => (x, .stay)) else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 2) : Config 1 2 a := ⟨s, fun _ => p, fun _ => f⟩

theorem write_hoare (x : Fin (a + 4)) (f : ℤ → Fin (a + 4)) (p : ℤ) :
    HoareTime (program x) (fun v => v = (cfg f p 0).tapes)
      (fun v => v = (cfg (Function.update f p x) p 0).tapes) 1 := by
  rintro v rfl
  refine ⟨1, cfg (Function.update f p x) p 1, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  rw [run_one]
  simp only [step, program, cfg, Tapes.start, Config.tapes, ↓reduceIte, Move.offset]
  congr 1
  congr 1
  · funext i; simp
  · funext i j
    by_cases hj : j = p
    · subst j; simp
    · simp [hj]

/-- Writing a bit on a blank cell places a one-bit word. -/
theorem update_blank (p : ℤ) (x : Fin (a + 4)) :
    Function.update (fun _ => (blank : Fin (a + 4))) p x = putWord (fun _ => blank) p [x] := by
  simp [putWord]

end IntegerMultBounds.Machine.WriteSymbol
