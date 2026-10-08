import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare

/-! Two-tape copying and moving of delimiter-terminated words. Every copied
symbol costs one actual transition. The finite control is independent of the
word length; arbitrary cells outside the two segments are preserved. -/

namespace IntegerMultBounds.Machine

namespace Copy

variable {a : ℕ}

def retained (erase : Bool) (x : Fin (a + 4)) : Fin (a + 4) :=
  if erase then blank else x

/-- Copy source tape zero to destination tape one until the delimiter, optionally
erasing each source symbol. Both heads finish on their respective next cells. -/
def program (stop : Fin (a + 4)) (erase : Bool) : Program 2 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if symbols 0 = stop then none else
    some (0, fun i => (if i = 0 then retained erase (symbols 0) else symbols 0, .right))

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) : Config 2 1 a where
  state := 0
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

theorem copy_step (stop : Fin (a + 4)) (erase : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p ≠ stop) :
    step (program stop erase) (cfg f g p q) =
      some (cfg (Function.update f p (retained erase (f p)))
        (Function.update g q (f p)) (p + 1) (q + 1)) := by
  simp only [step, program, cfg, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]

theorem copy_halt (stop : Fin (a + 4)) (erase : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) (h : f p = stop) :
    step (program stop erase) (cfg f g p q) = none := by
  simp [step, program, cfg, h]

/-- Exact execution over any delimiter-free word, including the empty word. -/
theorem copy_run (stop : Fin (a + 4)) (erase : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hxs : ∀ x ∈ xs, x ≠ stop) :
    run (program stop erase) xs.length (cfg (putWord f p xs) g p q) =
      some (cfg (putWord f p (xs.map (retained erase))) (putWord g q xs)
        (p + xs.length) (q + xs.length)) := by
  induction xs generalizing f g p q with
  | nil => simp [putWord, run]
  | cons x xs ih =>
    have hs := copy_step stop erase (putWord f p (x :: xs)) g p q
      (by rw [putWord_head]; exact hxs x (by simp))
    rw [putWord_head, putWord_replace_head] at hs
    simp only [List.length_cons, run, hs, Option.bind_some]
    have hr := ih (Function.update f p (retained erase x)) (Function.update g q x)
      (p + 1) (q + 1) (fun y hy => hxs y (by simp [hy]))
    simpa only [List.map_cons, ← putWord_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- The final delimiter is preserved, and the machine genuinely halts there. -/
theorem copy_exact (stop : Fin (a + 4)) (erase : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hxs : ∀ x ∈ xs, x ≠ stop) (hend : f (p + xs.length) = stop) :
    run (program stop erase) xs.length (cfg (putWord f p xs) g p q) =
      some (cfg (putWord f p (xs.map (retained erase))) (putWord g q xs)
        (p + xs.length) (q + xs.length)) ∧
    step (program stop erase)
      (cfg (putWord f p (xs.map (retained erase))) (putWord g q xs)
        (p + xs.length) (q + xs.length)) = none := by
  refine ⟨copy_run stop erase f g p q xs hxs, copy_halt stop erase _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hend]

def tapes (f g : ℤ → Fin (a + 4)) (p q : ℤ) : Tapes 2 a := (cfg f g p q).tapes

theorem copy_hoare (stop : Fin (a + 4)) (erase : Bool)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) (xs : List (Fin (a + 4)))
    (hxs : ∀ x ∈ xs, x ≠ stop) (hend : f (p + xs.length) = stop) :
    HoareTime (program stop erase)
      (fun v => v = tapes (putWord f p xs) g p q)
      (fun v => v = tapes (putWord f p (xs.map (retained erase))) (putWord g q xs)
        (p + xs.length) (q + xs.length)) xs.length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := copy_exact stop erase f g p q xs hxs hend
  exact ⟨xs.length, _, le_rfl, hr, hh, rfl⟩

/-- Copying to a blank tape produces the exact whole-tape output convention,
not merely a word followed by one blank. The source remains unchanged. -/
theorem copy_to_blank (stop : Fin (a + 4)) (f : ℤ → Fin (a + 4)) (p : ℤ)
    (xs : List (Fin (a + 4))) (hxs : ∀ x ∈ xs, x ≠ stop)
    (hend : f (p + xs.length) = stop) :
    run (program stop false) xs.length (cfg (putWord f p xs) (fun _ => blank) p 0) =
      some (cfg (putWord f p xs) (wordTape xs) (p + xs.length) xs.length) ∧
    step (program stop false)
      (cfg (putWord f p xs) (wordTape xs) (p + xs.length) xs.length) = none := by
  have hw : putWord (fun _ => blank) 0 xs = wordTape xs := by
    funext j
    simpa using putWord_blank 0 j xs
  have hr : (retained false : Fin (a + 4) → Fin (a + 4)) = id := by funext x; rfl
  simpa only [hr, List.map_id, hw, zero_add] using
    copy_exact stop false f (fun _ => blank) p 0 xs hxs hend

end Copy

end IntegerMultBounds.Machine
