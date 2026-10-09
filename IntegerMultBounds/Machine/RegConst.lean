import IntegerMultBounds.Machine.Registers

/-! Writing a fixed word on a blank register: the state counts the bits
written; then the head returns to the origin. -/

namespace IntegerMultBounds.Machine.RegConst

open Registers (one canon canon_value reg)

variable {a : ℕ}

/-- Write the bits of `w` left to right. -/
def writer (w : List Bool) : Program 1 (w.length + 1) a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ =>
    if h : (s : ℕ) < w.length then
      some (⟨s + 1, by omega⟩, fun _ => (bitSymbol (w.get ⟨s, h⟩), .right))
    else none

theorem pw_snoc (A : List (Fin (a + 4))) (x : Fin (a + 4)) :
    putWord (fun _ => blank) 0 (A ++ [x]) = Function.update (putWord (fun _ => blank) 0 A) (A.length : ℤ) x := by
  rw [← putWord_append_forward, zero_add]
  rfl

theorem writer_step (w : List Bool) (k : ℕ) (hk : k < w.length) (T : ℤ → Fin (a + 4)) :
    step (writer (a := a) w) ⟨⟨k, by omega⟩, fun _ => (k : ℤ), fun _ => T⟩ =
      some ⟨⟨k + 1, by omega⟩, fun _ => ((k + 1 : ℕ) : ℤ), fun _ => Function.update T (k : ℤ) (bitSymbol w[k])⟩ := by
  unfold step
  simp only [writer, hk, ↓reduceDIte, Move.offset]
  congr 1
  congr 1
  funext _ j
  by_cases hj : j = (k : ℤ)
  · subst hj; simp
  · simp [hj, Function.update_of_ne hj]

theorem writer_run (w : List Bool) (k : ℕ) (hk : k ≤ w.length) :
    run (writer (a := a) w) k ⟨0, fun _ => 0, fun _ => fun _ => blank⟩ =
      some ⟨⟨k, by omega⟩, fun _ => (k : ℤ), fun _ => putWord (fun _ => blank) 0 ((w.take k).map bitSymbol)⟩ := by
  induction k with
  | zero => simp [run, putWord]
  | succ k ih =>
    have hk' : k < w.length := by omega
    rw [run_add, ih (by omega), Option.bind_some, run_one, writer_step w k hk']
    congr 2
    funext _
    rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some, List.map_append,
      List.map_singleton, pw_snoc, List.length_map, List.length_take, min_eq_left hk'.le]

/-- The register of a constant: write its canonical word and return. -/
def program (n : ℕ) := seq (writer (a := a) (canon n)) (ReturnOrigin.program (a := a))

theorem const_hoare (n : ℕ) :
    HoareTime (program (a := a) n) (fun v => v = one (fun _ => blank) 0) (fun v => v = one (reg n) 0)
      (2 * (canon n).length + 3) := by
  have h1 : HoareTime (writer (a := a) (canon n)) (fun v => v = one (fun _ => blank) 0)
      (fun v => v = one (reg n) ((canon n).length : ℤ)) (canon n).length := by
    rintro v rfl
    refine ⟨(canon n).length, _, le_rfl, writer_run (canon n) _ le_rfl, ?_, ?_⟩
    · simp [step, writer]
    · simp [reg, one, Config.tapes, List.take_length]
  have h2 : HoareTime (ReturnOrigin.program (a := a)) (fun v => v = one (reg n) ((canon n).length : ℤ))
      (fun v => v = one (reg n) 0) ((canon n).length + 2) := by
    have := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin (a + 4))) 0 ((canon n).map bitSymbol)
      (ReturnOrigin.bits_nonblank _) rfl
    simp only [List.length_map, zero_add] at this
    exact this
  exact (h1.seq h2).consequence (fun v hv => hv) (fun v hv => hv) (by omega)

end IntegerMultBounds.Machine.RegConst
