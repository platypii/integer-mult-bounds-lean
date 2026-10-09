import IntegerMultBounds.Machine.RecordTape
import Mathlib.Data.List.GetD

/-! Rewinding (and optionally erasing) a tape of blank-separated records: from
any cell, step left once, then scan left until two consecutive blanks, the
blank run to the left of the first record; return to the first record's
origin. With `er` every visited cell is blanked, so a record tape is erased
completely when the scan starts at its end. -/

namespace IntegerMultBounds.Machine.RecordRewind

variable {a : ℕ}

/-- State four: first step left; zero: scanning; one: a blank was just read;
two: return; three: halted. -/
def program (er : Bool) : Program 1 5 a where
  tapes_pos := by decide
  start := 4
  transition := fun s symbols =>
    let c : Fin (a + 4) := if er then blank else symbols 0
    if s = 4 then some (0, fun _ => (c, .left))
    else if s = 0 then
      if symbols 0 = blank then some (1, fun _ => (c, .left)) else some (0, fun _ => (c, .left))
    else if s = 1 then
      if symbols 0 = blank then some (2, fun _ => (c, .right)) else some (0, fun _ => (c, .left))
    else if s = 2 then some (3, fun _ => (c, .right))
    else none

def cfg (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin 5) : Config 1 5 a := ⟨s, fun _ => p, fun _ => f⟩

/-- The tape after visiting the cells `(x, x0]`. -/
def wipe (er : Bool) (f : ℤ → Fin (a + 4)) (x x0 : ℤ) : ℤ → Fin (a + 4) :=
  fun y => if er ∧ x < y ∧ y ≤ x0 then blank else f y

theorem wipe_at (er : Bool) (f : ℤ → Fin (a + 4)) (x x0 : ℤ) : wipe er f x x0 x = f x := by
  simp [wipe]

theorem wipe_update (er : Bool) (f : ℤ → Fin (a + 4)) (x x0 : ℤ) (hx : x ≤ x0) :
    (fun j => if j = x then (if er then blank else wipe er f x x0 x) else wipe er f x x0 j) =
      wipe er f (x - 1) x0 := by
  funext j
  unfold wipe
  by_cases hj : j = x
  · subst hj; cases er <;> simp [hx]
  · have : (x - 1 < j) ↔ (x < j) := by omega
    cases er <;> simp [hj, this]

theorem step_gen (er : Bool) (f : ℤ → Fin (a + 4)) (x x0 : ℤ) (s s' : Fin 5) (mv : Move)
    (ht : (program (a := a) er).transition s (fun _ => wipe er f x x0 x) =
      some (s', fun _ => (if er then blank else wipe er f x x0 x, mv))) (hx : x ≤ x0) :
    step (program er) (cfg (wipe er f x x0) x s) = some (cfg (wipe er f (x - 1) x0) (x + mv.offset) s') := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq]
  congr 1
  funext _
  exact wipe_update er f x x0 hx

theorem step_first (er : Bool) (f : ℤ → Fin (a + 4)) (x0 : ℤ) :
    step (program er) (cfg (wipe er f x0 x0) x0 4) = some (cfg (wipe er f (x0 - 1) x0) (x0 - 1) 0) := by
  have := step_gen er f x0 x0 4 0 .left (by simp [program]) le_rfl
  rw [this]; simp only [Move.offset]; congr 2

variable (er : Bool) (f : ℤ → Fin (a + 4)) (x0 : ℤ)
  (hb1 : f (-1) = blank) (hb2 : f (-2) = blank)

include hb1 hb2 in
/-- The scan from state zero or one ends at the origin in `x + 4` steps. -/
theorem scan_run (n : ℕ) (x : ℤ) (hn : x + 2 = n) (hx0 : x < x0) (s : Fin 5)
    (hD : ∀ y, 0 ≤ y → y ≤ x → f y = blank → f (y - 1) ≠ blank)
    (hs0 : s = 0 → -1 ≤ x) (hs1 : s = 1 → (0 ≤ x + 1 → f x ≠ blank))
    (hs : s = 0 ∨ s = 1) :
    run (program er) (n + 2) (cfg (wipe er f x x0) x s) = some (cfg (wipe er f (-1) x0) 0 3) := by
  induction n generalizing x s with
  | zero =>
    have hx : x = -2 := by omega
    subst hx
    rcases hs with rfl | rfl
    · have := hs0 rfl; omega
    · have hw3 : wipe er f (-2 - 1) x0 = wipe er f (-1) x0 := by
        funext y; unfold wipe
        by_cases h1 : y = -2
        · subst h1; cases er <;> simp [hb2]
        by_cases h2 : y = -1
        · subst h2; cases er <;> simp [hb1]
        cases er <;> simp only [Bool.false_eq_true, false_and, ite_false, true_and]
        all_goals split_ifs <;> first | rfl | (exfalso; omega)
      have hw2 : wipe er f (-1 - 1) x0 = wipe er f (-1) x0 := by
        funext y; unfold wipe
        by_cases h2 : y = -1
        · subst h2; cases er <;> simp [hb1]
        cases er <;> simp only [Bool.false_eq_true, false_and, ite_false, true_and]
        all_goals split_ifs <;> first | rfl | (exfalso; omega)
      have h1 := step_gen er f (-2) x0 1 2 .right (by simp [program, wipe_at, hb2]) (by omega)
      have h2 := step_gen er f (-1) x0 2 3 .right (by simp [program]) (by omega)
      rw [hw3] at h1
      rw [hw2] at h2
      rw [run, h1]
      simp only [Option.bind_some, Move.offset]
      rw [show (-2 : ℤ) + 1 = -1 by norm_num, run, h2]
      simp [Move.offset, run]
  | succ n ih =>
    have hxm : -1 ≤ x := by omega
    have hfx : f x = blank → x ≠ -1 → 0 ≤ x := fun _ h => by omega
    rcases hs with rfl | rfl
    · by_cases hb : f x = blank
      · have hst := step_gen er f x x0 0 1 .left (by simp [program, wipe_at, hb]) hx0.le
        rw [show n + 1 + 2 = (n + 2) + 1 by ring, run, hst]
        simp only [Option.bind_some, Move.offset]
        rw [show x + -1 = x - 1 by ring]
        refine ih (x - 1) (by omega) (by omega) 1 (fun y h0 hy => hD y h0 (by omega))
          (by intro h; exact absurd h (by decide)) (fun _ h0 => ?_) (Or.inr rfl)
        have hx0' : 0 ≤ x := by omega
        have := hD x hx0' le_rfl hb
        exact this
      · have hx' : 0 ≤ x := by
          by_contra h
          have : x = -1 := by omega
          subst this; exact hb hb1
        have hst := step_gen er f x x0 0 0 .left (by simp [program, wipe_at, hb]) hx0.le
        rw [show n + 1 + 2 = (n + 2) + 1 by ring, run, hst]
        simp only [Option.bind_some, Move.offset]
        rw [show x + -1 = x - 1 by ring]
        exact ih (x - 1) (by omega) (by omega) 0 (fun y h0 hy => hD y h0 (by omega))
          (fun _ => by omega) (by intro h; exact absurd h (by decide)) (Or.inl rfl)
    · have hb := hs1 rfl (by omega)
      have hx' : 0 ≤ x := by
        by_contra h
        have : x = -1 := by omega
        subst this; exact hb hb1
      have hst := step_gen er f x x0 1 0 .left (by simp [program, wipe_at, hb]) hx0.le
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, run, hst]
      simp only [Option.bind_some, Move.offset]
      rw [show x + -1 = x - 1 by ring]
      exact ih (x - 1) (by omega) (by omega) 0 (fun y h0 hy => hD y h0 (by omega))
        (fun _ => by omega) (by intro h; exact absurd h (by decide)) (Or.inl rfl)

include hb1 hb2 in
/-- The contract on any tape: from head `x0 ≥ 0`, with no two adjacent blanks in
`[-1, x0)` except at the left end, the head returns to `0` in `x0 + 4` steps;
with `er` the cells `[0, x0]` are blanked. -/
theorem rewind_hoare (hx0 : 0 ≤ x0)
    (hD : ∀ y, 0 ≤ y → y ≤ x0 - 1 → f y = blank → f (y - 1) ≠ blank) :
    HoareTime (program er) (fun v => v = (cfg f x0 0).tapes)
      (fun v => v = (cfg (wipe er f (-1) x0) 0 0).tapes) (x0.toNat + 4) := by
  rintro v rfl
  refine ⟨x0.toNat + 4, cfg (wipe er f (-1) x0) 0 3, le_rfl, ?_, by simp [step, program, cfg], rfl⟩
  have h0 : (cfg f x0 0).tapes.start (program er) = cfg (wipe er f x0 x0) x0 4 := by
    simp only [Tapes.start, cfg, Config.tapes, program]
    congr 2
    funext _ y; simp [wipe]
  rw [h0, show x0.toNat + 4 = (x0.toNat + 1 + 2) + 1 by ring, run, step_first]
  simp only [Option.bind_some]
  exact scan_run er f x0 hb1 hb2 (x0.toNat + 1) (x0 - 1) (by omega) (by omega) 0 hD
    (fun _ => by omega) (by intro h; exact absurd h (by decide)) (Or.inl rfl)

section Records

open OrderedSelect (flat flat_cons inTape)

theorem getD_mem_ne (r : List (Fin (a + 4))) (hr : ∀ x ∈ r, x ≠ blank) (k : ℕ) (hk : k < r.length) :
    r.getD k blank ≠ blank := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hr _ (List.getElem_mem hk)

/-- In flattened records, the first symbol is not blank and no two blanks are adjacent. -/
theorem flat_adj (recs : List (List (Fin (a + 4))))
    (hne : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) :
    (0 < (flat recs).length → (flat recs).getD 0 blank ≠ blank) ∧
      ∀ k, k + 1 < (flat recs).length → (flat recs).getD (k + 1) blank = blank →
        (flat recs).getD k blank ≠ blank := by
  induction recs with
  | nil => simp [OrderedSelect.flat_nil]
  | cons r rs ih =>
    obtain ⟨hr0, hrb⟩ := hne r (by simp)
    obtain ⟨ih0, ih1⟩ := ih (fun r' h => hne r' (by simp [h]))
    have hrl : 0 < r.length := List.length_pos_of_ne_nil hr0
    rw [flat_cons]
    refine ⟨fun _ => ?_, fun k hk hb => ?_⟩
    · rw [List.getD_append _ _ _ _ hrl]; exact getD_mem_ne r hrb 0 hrl
    · rcases Nat.lt_or_ge (k + 1) r.length with h | h
      · rw [List.getD_append _ _ _ _ (by omega)]; exact getD_mem_ne r hrb k (by omega)
      rcases Nat.lt_or_ge k r.length with h' | h'
      · rw [List.getD_append _ _ _ _ h']; exact getD_mem_ne r hrb k h'
      · rw [List.getD_append_right _ _ _ _ h] at hb
        rw [List.getD_append_right _ _ _ _ h']
        simp only [List.length_append, List.length_cons] at hk
        obtain ⟨j, hj⟩ : ∃ j, k = r.length + j := ⟨k - r.length, by omega⟩
        subst hj
        rcases j with _ | j
        · rw [show r.length + 0 + 1 - r.length = 0 + 1 by omega, List.getD_cons_succ] at hb
          exact absurd hb (ih0 (by omega))
        · rw [show r.length + (j + 1) + 1 - r.length = (j + 1) + 1 by omega, List.getD_cons_succ] at hb
          rw [show r.length + (j + 1) - r.length = j + 1 by omega, List.getD_cons_succ]
          exact ih1 j (by omega) hb

theorem putWord_getElem' (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (k : ℕ)
    (hk : k < xs.length) : putWord f p xs (p + k) = xs[k] := by
  induction xs generalizing f p k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [putWord_head]
    | succ k =>
      rw [putWord_cons, show p + ((k + 1 : ℕ) : ℤ) = p + 1 + k by omega,
        ih _ (p + 1) k (by simpa using hk)]
      rfl

theorem inTape_eq (recs : List (List (Fin (a + 4)))) (k : ℕ) :
    inTape recs (k : ℤ) = (flat recs).getD k blank := by
  rcases Nat.lt_or_ge k (flat recs).length with h | h
  · have := putWord_getElem' (fun _ => (blank : Fin (a + 4))) 0 (flat recs) k h
    rw [zero_add] at this
    rw [inTape, this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  · rw [inTape, putWord_outside _ _ _ _ (Or.inr (by omega)), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none h]
    rfl

/-- A record tape satisfies the rewind hypothesis up to its end. -/
theorem inTape_adj (recs : List (List (Fin (a + 4))))
    (hne : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) (y : ℤ) (hy0 : 0 ≤ y)
    (hy : y < (flat recs).length) (hb : inTape recs y = blank) : inTape recs (y - 1) ≠ blank := by
  obtain ⟨h0, h1⟩ := flat_adj recs hne
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, y = k := ⟨y.toNat, by omega⟩
  rw [inTape_eq] at hb
  rcases k with _ | k
  · exact absurd hb (h0 (by omega))
  · rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, inTape_eq]
    exact h1 k (by omega) hb

theorem inTape_neg (recs : List (List (Fin (a + 4)))) (y : ℤ) (hy : y < 0) : inTape recs y = blank := by
  rw [inTape, putWord_outside _ _ _ _ (Or.inl hy)]

/-- Rewinding a record tape from any cell up to its end. -/
theorem rewind_records (recs : List (List (Fin (a + 4))))
    (hne : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) (x0 : ℤ) (hx0 : 0 ≤ x0)
    (hx : x0 ≤ (flat recs).length) :
    HoareTime (program false) (fun v => v = (cfg (inTape recs) x0 0).tapes)
      (fun v => v = (cfg (inTape recs) 0 0).tapes) (x0.toNat + 4) := by
  have h := rewind_hoare false (inTape recs) x0 (inTape_neg recs _ (by norm_num))
    (inTape_neg recs _ (by norm_num)) hx0
    (fun y hy0 hy hb => inTape_adj recs hne y hy0 (by omega) hb)
  have hw : wipe false (inTape recs) (-1) x0 = inTape recs := by funext y; simp [wipe]
  rwa [hw] at h

/-- Erasing a record tape from its end. -/
theorem erase_records (recs : List (List (Fin (a + 4))))
    (hne : ∀ r ∈ recs, r ≠ [] ∧ ∀ x ∈ r, x ≠ blank) :
    HoareTime (program true) (fun v => v = (cfg (inTape recs) (flat recs).length 0).tapes)
      (fun v => v = (cfg (fun _ => blank) 0 0).tapes) ((flat recs).length + 4) := by
  have h := rewind_hoare true (inTape recs) (flat recs).length (inTape_neg recs _ (by norm_num))
    (inTape_neg recs _ (by norm_num)) (by omega)
    (fun y hy0 hy hb => inTape_adj recs hne y hy0 (by omega) hb)
  have hw : wipe true (inTape recs) (-1) (flat recs).length = fun _ => blank := by
    funext y; unfold wipe
    by_cases h1 : -1 < y ∧ y ≤ (flat recs).length
    · simp [h1]
    · simp only [h1, and_false, ite_false]
      rcases not_and_or.mp h1 with h2 | h2
      · exact inTape_neg recs y (by omega)
      · rw [inTape, putWord_outside _ _ _ _ (Or.inr (by omega))]
  rwa [hw] at h

end Records

end IntegerMultBounds.Machine.RecordRewind
