import IntegerMultBounds.Machine.NeumannStepLemmas

/-! Joining and splitting complex records in place. A complex coordinate is
two blank-separated words (real, imaginary); joined, it is one record
`re ++ separator :: im`. The join machine scans right and writes a separator
over every other blank; the split machine writes a blank over every
separator. Both stop on the blank after the last record. They let the
record-selecting machine move complex coordinates as single records. -/

namespace IntegerMultBounds.Machine.PairJoin

open OrderedSelect (inTape flat flat_cons flat_nil)
open GaussianLine (wordRecs)

variable {a : ℕ}

/-- Consecutive words joined in pairs. -/
def pairs : List (List Bool) → List (List (Fin (a + 4)))
  | x :: y :: rest => (x.map bitSymbol ++ separator :: y.map bitSymbol) :: pairs rest
  | _ => []

/-- Join: state zero at a pair origin, one in the real word, two in the imaginary word. -/
def joinProgram : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 then
      if sy 0 = blank then none else some (1, fun _ => (sy 0, .right))
    else if s = 1 then
      if sy 0 = blank then some (2, fun _ => (separator, .right)) else some (1, fun _ => (sy 0, .right))
    else
      if sy 0 = blank then some (0, fun _ => (sy 0, .right)) else some (2, fun _ => (sy 0, .right))

/-- Split: state zero at a record origin, one inside. -/
def splitProgram : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy =>
    if s = 0 ∧ sy 0 = blank then none
    else if sy 0 = blank ∨ sy 0 = separator then some (0, fun _ => (blank, .right))
    else some (1, fun _ => (sy 0, .right))

def cfg {q : ℕ} (f : ℤ → Fin (a + 4)) (p : ℤ) (s : Fin q) : Config 1 q a := ⟨s, fun _ => p, fun _ => f⟩

theorem sep_ne_blank : (separator : Fin (a + 4)) ≠ blank := by simp [separator, blank]

theorem bit_ne_sep (b : Bool) : (bitSymbol b : Fin (a + 4)) ≠ separator := by
  cases b <;> simp [bitSymbol, separator]

/-- A step that writes `x` at the head and moves right. -/
theorem step_write {q : ℕ} (M : Program 1 q a) (f : ℤ → Fin (a + 4)) (p : ℤ) (s s' : Fin q) (x : Fin (a + 4))
    (ht : M.transition s (fun _ => f p) = some (s', fun _ => (x, Move.right))) :
    step M (cfg f p s) = some (cfg (Function.update f p x) (p + 1) s') := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq, Move.offset]
  congr 1
  funext _ j
  by_cases hj : j = p <;> simp [hj, Function.update_apply]

theorem update_same (f : ℤ → Fin (a + 4)) (p : ℤ) : Function.update f p (f p) = f := by
  funext j; by_cases hj : j = p <;> simp [hj, Function.update_apply]

/-- Scanning a word of bits in a state that keeps its symbols. -/
theorem scan_bits {q : ℕ} (M : Program 1 q a) (s : Fin q)
    (hM : ∀ b : Bool, M.transition s (fun _ => bitSymbol b) = some (s, fun _ => (bitSymbol b, Move.right)))
    (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List Bool)
    (hf : ∀ k : ℕ, k < xs.length → f (p + k) = bitSymbol (xs.getD k false)) :
    run M xs.length (cfg f p s) = some (cfg f (p + xs.length) s) := by
  induction xs generalizing p with
  | nil => simp [run]
  | cons b xs ih =>
    have h0 : f p = bitSymbol b := by simpa using hf 0 (by simp)
    rw [List.length_cons, run, step_write M f p s s (bitSymbol b) (by rw [h0]; exact hM b), ← h0,
      update_same]
    simp only [Option.bind_some]
    rw [ih (p + 1) (fun k hk => by
      rw [show p + 1 + (k : ℤ) = p + ((k + 1 : ℕ) : ℤ) by push_cast; ring, hf (k + 1) (by simp; omega)]; simp)]
    congr 2; push_cast; ring

section Lists

theorem pw_get (L : List (Fin (a + 4))) (k : ℕ) : putWord (fun _ => blank) 0 L (k : ℤ) = L.getD k blank := by
  rcases Nat.lt_or_ge k L.length with h | h
  · have := RecordRewind.putWord_getElem' (fun _ => (blank : Fin (a + 4))) 0 L k h
    rw [zero_add] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  · rw [putWord_outside _ _ _ _ (Or.inr (by omega)), List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rfl

theorem pw_bits (A B : List (Fin (a + 4))) (c : List Bool) (k : ℕ) (hk : k < c.length) :
    putWord (fun _ => blank) 0 (A ++ c.map bitSymbol ++ B) (((A.length : ℕ) : ℤ) + k) =
      bitSymbol (c.getD k false) := by
  rw [← Nat.cast_add, pw_get, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by simp; omega), show A.length + k - A.length = k by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem pw_at (A B : List (Fin (a + 4))) (x : Fin (a + 4)) :
    putWord (fun _ => blank) 0 (A ++ x :: B) ((A.length : ℕ) : ℤ) = x := by
  rw [pw_get, List.getD_append_right _ _ _ _ le_rfl]; simp

theorem pw_update (A B : List (Fin (a + 4))) (x y : Fin (a + 4)) :
    Function.update (putWord (fun _ => blank) 0 (A ++ x :: B)) ((A.length : ℕ) : ℤ) y =
      putWord (fun _ => blank) 0 (A ++ y :: B) := by
  funext j
  by_cases hj : j = ((A.length : ℕ) : ℤ)
  · subst hj; rw [Function.update_self, pw_at]
  · rw [Function.update_of_ne hj]
    rcases lt_or_ge j 0 with h0 | h0
    · rw [putWord_outside _ _ _ _ (Or.inl h0), putWord_outside _ _ _ _ (Or.inl h0)]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k := ⟨j.toNat, by omega⟩
      have hk : k ≠ A.length := by intro h; exact hj (by rw [h])
      rw [pw_get, pw_get]
      rcases Nat.lt_or_ge k A.length with h | h
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
      · rw [List.getD_append_right _ _ _ _ h, List.getD_append_right _ _ _ _ h]
        obtain ⟨i, hi⟩ : ∃ i, k - A.length = i + 1 := ⟨k - A.length - 1, by omega⟩
        rw [hi]; simp

end Lists

section Join

theorem flat_two (x y : List Bool) (rest : List (List Bool)) :
    flat (wordRecs (a := a) (x :: y :: rest)) =
      x.map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: flat (wordRecs (a := a) rest)) := by
  simp [wordRecs, flat_cons]

theorem pairs_two (x y : List Bool) (rest : List (List Bool)) :
    flat (pairs (a := a) (x :: y :: rest)) =
      x.map bitSymbol ++ separator :: (y.map bitSymbol ++ blank :: flat (pairs (a := a) rest)) := by
  simp [pairs, flat_cons]

theorem join_t1 (b : Bool) : (joinProgram (a := a)).transition 1 (fun _ => bitSymbol b) =
    some (1, fun _ => (bitSymbol b, Move.right)) := by
  cases b <;> simp [joinProgram, bitSymbol, blank]

theorem join_t2 (b : Bool) : (joinProgram (a := a)).transition 2 (fun _ => bitSymbol b) =
    some (2, fun _ => (bitSymbol b, Move.right)) := by
  cases b <;> simp [joinProgram, bitSymbol, blank]

/-- One pair: the real word, the blank (written over by a separator), the
imaginary word, the blank. -/
theorem pair_run (D F : List (Fin (a + 4))) (b : Bool) (xs y : List Bool) :
    run joinProgram (1 + (xs.length + (1 + (y.length + 1))))
        (cfg (putWord (fun _ => blank) 0 (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: F))))
          D.length 0) =
      some (cfg (putWord (fun _ => blank) 0 (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (y.map bitSymbol ++ blank :: F))))
        (D.length + (1 + (xs.length + (1 + (y.length + 1))))) 0) := by
  set T := putWord (fun _ => (blank : Fin (a + 4))) 0 (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: F)))
  -- the first bit
  rw [run_add, run_one, step_write joinProgram T _ 0 1 (bitSymbol b) (by
      simp only [T]; rw [pw_at]; cases b <;> simp [joinProgram, bitSymbol, blank])]
  simp only [Option.bind_some]
  have hT0 : Function.update T (D.length : ℤ) (bitSymbol b) = T := by
    simp only [T]; rw [pw_update]
  rw [hT0]
  -- the rest of the real word
  have eA : D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: F)) =
      (D ++ [bitSymbol b]) ++ xs.map bitSymbol ++ (blank :: (y.map bitSymbol ++ blank :: F)) := by simp
  rw [run_add, scan_bits joinProgram 1 join_t1 T _ xs (fun k hk => by
      simp only [T]; rw [eA, show (D.length : ℤ) + 1 + k = (((D ++ [bitSymbol b]).length : ℕ) : ℤ) + k by simp,
        pw_bits _ _ _ _ hk])]
  simp only [Option.bind_some]
  -- the blank between the words
  have eB : D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: F)) =
      (D ++ bitSymbol b :: xs.map bitSymbol) ++ blank :: (y.map bitSymbol ++ blank :: F) := by simp
  have hpos : (D.length : ℤ) + 1 + xs.length = (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) := by
    simp; ring
  rw [run_add, run_one, hpos, step_write joinProgram T _ 1 2 separator (by
      simp only [T]; rw [eB, pw_at]; simp [joinProgram])]
  simp only [Option.bind_some]
  have hT1 : Function.update T (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) separator =
      putWord (fun _ => blank) 0 ((D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: (y.map bitSymbol ++ blank :: F)) := by
    simp only [T]; rw [eB, pw_update]
  rw [hT1]
  -- the imaginary word
  have eC : (D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: (y.map bitSymbol ++ blank :: F) =
      ((D ++ bitSymbol b :: xs.map bitSymbol) ++ [separator]) ++ y.map bitSymbol ++ (blank :: F) := by simp
  rw [run_add, scan_bits joinProgram 2 join_t2 _ _ y (fun k hk => by
      rw [eC]
      convert pw_bits ((D ++ bitSymbol b :: xs.map bitSymbol) ++ [separator]) (blank :: F) y k hk using 2
      simp; ring)]
  simp only [Option.bind_some]
  -- the final blank
  have hpos2 : (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) + 1 + y.length =
      ((((D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: y.map bitSymbol).length : ℕ) : ℤ) := by
    simp; ring
  have eD : (D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: (y.map bitSymbol ++ blank :: F) =
      ((D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: y.map bitSymbol) ++ blank :: F := by simp
  rw [run_one, hpos2, eD, step_write joinProgram _ _ 2 0 blank (by rw [pw_at]; simp [joinProgram]), pw_update]
  congr 2
  · simp
  · simp; ring

theorem join_run (n : ℕ) : ∀ (ws : List (List Bool)), ws.length = 2 * n → (∀ x ∈ ws, x ≠ []) →
    ∀ D : List (Fin (a + 4)),
    run joinProgram (flat (wordRecs (a := a) ws)).length
        (cfg (putWord (fun _ => blank) 0 (D ++ flat (wordRecs (a := a) ws))) D.length 0) =
      some (cfg (putWord (fun _ => blank) 0 (D ++ flat (pairs (a := a) ws)))
        (D.length + (flat (wordRecs (a := a) ws)).length) 0) := by
  induction n with
  | zero =>
    intro ws hl _ D
    obtain rfl : ws = [] := List.length_eq_zero_iff.mp (by omega)
    simp [wordRecs, pairs, flat_nil, run]
  | succ n ih =>
    intro ws hl hne D
    obtain ⟨x, y, rest, rfl⟩ : ∃ x y rest, ws = x :: y :: rest := by
      match ws, hl with
      | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
    obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
    have hrl : rest.length = 2 * n := by simp at hl; omega
    rw [flat_two, pairs_two]
    have hlen : ((b :: xs).map bitSymbol ++ blank :: (y.map bitSymbol ++ blank :: flat (wordRecs (a := a) rest))).length =
        (1 + (xs.length + (1 + (y.length + 1)))) + (flat (wordRecs (a := a) rest)).length := by simp; ring
    rw [hlen, run_add, List.map_cons, List.cons_append, pair_run]
    simp only [Option.bind_some]
    have e1 : D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (y.map bitSymbol ++ blank :: flat (wordRecs (a := a) rest))) =
        (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (y.map bitSymbol ++ [blank]))) ++ flat (wordRecs (a := a) rest) := by simp
    have hl1 : D.length + (1 + (xs.length + (1 + (y.length + 1)))) =
        (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (y.map bitSymbol ++ [blank]))).length := by simp; ring
    have key := ih rest hrl (fun z hz => hne z (by simp [hz]))
      (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (y.map bitSymbol ++ [blank])))
    rw [e1]
    convert key using 3
    · rw [← hl1]; push_cast; ring
    · simp
    · simp; ring

theorem flat_pairs_length (n : ℕ) : ∀ (ws : List (List Bool)), ws.length = 2 * n →
    (flat (pairs (a := a) ws)).length = (flat (wordRecs (a := a) ws)).length := by
  induction n with
  | zero =>
    intro ws hl
    obtain rfl : ws = [] := List.length_eq_zero_iff.mp (by omega)
    rfl
  | succ n ih =>
    intro ws hl
    obtain ⟨x, y, rest, rfl⟩ : ∃ x y rest, ws = x :: y :: rest := by
      match ws, hl with
      | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
    rw [flat_two, pairs_two]
    simp [ih rest (by simp at hl; omega)]

/-- The join contract: the word records of `2n` words become `n` joined records. -/
theorem join_hoare (n : ℕ) (ws : List (List Bool)) (hl : ws.length = 2 * n) (hne : ∀ x ∈ ws, x ≠ []) :
    HoareTime (joinProgram (a := a)) (fun v => v = (cfg (inTape (wordRecs (a := a) ws)) 0 (0 : Fin 3)).tapes)
      (fun v => v = (cfg (inTape (pairs (a := a) ws)) (flat (wordRecs (a := a) ws)).length (0 : Fin 3)).tapes)
      (flat (wordRecs (a := a) ws)).length := by
  rintro v rfl
  have h := join_run (a := a) n ws hl hne []
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at h
  refine ⟨_, _, le_rfl, h, ?_, rfl⟩
  unfold step
  have hb : putWord (fun _ => (blank : Fin (a + 4))) 0 (flat (pairs (a := a) ws))
      ((flat (wordRecs (a := a) ws)).length : ℤ) = blank := by
    rw [← flat_pairs_length n ws hl, pw_get]; simp
  simp [cfg, joinProgram, hb]

end Join

section Split

theorem split_t1 (b : Bool) : (splitProgram (a := a)).transition 1 (fun _ => bitSymbol b) =
    some (1, fun _ => (bitSymbol b, Move.right)) := by
  cases b <;> simp [splitProgram, bitSymbol, blank, separator]

theorem split_bit (s : Fin 2) (b : Bool) : (splitProgram (a := a)).transition s (fun _ => bitSymbol b) =
    some (1, fun _ => (bitSymbol b, Move.right)) := by
  fin_cases s <;> cases b <;> simp [splitProgram, bitSymbol, blank, separator]

/-- One joined pair is split back into two word records. -/
theorem split_pair_run (D F : List (Fin (a + 4))) (b c : Bool) (xs ys : List Bool) :
    run splitProgram (1 + (xs.length + (1 + (1 + (ys.length + 1)))))
        (cfg (putWord (fun _ => blank) 0
          (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F)))))
          D.length 0) =
      some (cfg (putWord (fun _ => blank) 0
          (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F)))))
        (D.length + (1 + (xs.length + (1 + (1 + (ys.length + 1)))))) 0) := by
  set T := putWord (fun _ => (blank : Fin (a + 4))) 0
    (D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F))))
  rw [run_add, run_one, step_write splitProgram T _ 0 1 (bitSymbol b) (by simp only [T]; rw [pw_at]; exact split_bit 0 b)]
  simp only [Option.bind_some]
  have hT0 : Function.update T (D.length : ℤ) (bitSymbol b) = T := by simp only [T]; rw [pw_update]
  rw [hT0]
  have eA : D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F))) =
      (D ++ [bitSymbol b]) ++ xs.map bitSymbol ++ (separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F))) := by simp
  rw [run_add, scan_bits splitProgram 1 split_t1 T _ xs (fun k hk => by
      simp only [T]; rw [eA]
      convert pw_bits (D ++ [bitSymbol b]) _ xs k hk using 2
      simp)]
  simp only [Option.bind_some]
  have eB : D ++ bitSymbol b :: (xs.map bitSymbol ++ separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F))) =
      (D ++ bitSymbol b :: xs.map bitSymbol) ++ separator :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F)) := by simp
  have hpos : (D.length : ℤ) + 1 + xs.length = (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) := by
    simp; ring
  rw [run_add, run_one, hpos, step_write splitProgram T _ 1 0 blank (by
      simp only [T]; rw [eB, pw_at]; simp [splitProgram, separator, blank])]
  simp only [Option.bind_some]
  have hT1 : Function.update T (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) blank =
      putWord (fun _ => blank) 0 ((D ++ bitSymbol b :: xs.map bitSymbol) ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F))) := by
    simp only [T]; rw [eB, pw_update]
  rw [hT1]
  have eC : (D ++ bitSymbol b :: xs.map bitSymbol) ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: F)) =
      ((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ bitSymbol c :: (ys.map bitSymbol ++ blank :: F) := by simp
  have hpos1 : (((D ++ bitSymbol b :: xs.map bitSymbol).length : ℕ) : ℤ) + 1 =
      ((((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]).length : ℕ) : ℤ) := by simp <;> ring
  rw [run_add, run_one, hpos1, eC, step_write splitProgram _ _ 0 1 (bitSymbol c) (by rw [pw_at]; exact split_bit 0 c),
    pw_update]
  simp only [Option.bind_some]
  have eD : ((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ bitSymbol c :: (ys.map bitSymbol ++ blank :: F) =
      (((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ [bitSymbol c]) ++ ys.map bitSymbol ++ (blank :: F) := by simp
  rw [run_add, eD, scan_bits splitProgram 1 split_t1 _ _ ys (fun k hk => by
      convert pw_bits (((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ [bitSymbol c]) _ ys k hk using 2
      simp <;> ring)]
  simp only [Option.bind_some]
  have hpos2 : ((((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]).length : ℕ) : ℤ) + 1 + ys.length =
      (((((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ [bitSymbol c]) ++ ys.map bitSymbol).length : ℕ) := by
    simp; ring
  have eE : (((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ [bitSymbol c]) ++ ys.map bitSymbol ++ (blank :: F) =
      ((((D ++ bitSymbol b :: xs.map bitSymbol) ++ [blank]) ++ [bitSymbol c]) ++ ys.map bitSymbol) ++ blank :: F := by simp
  rw [run_one, hpos2, eE, step_write splitProgram _ _ 1 0 blank (by rw [pw_at]; simp [splitProgram]), pw_update]
  congr 2
  · simp
  · simp; ring

theorem split_run (n : ℕ) : ∀ (ws : List (List Bool)), ws.length = 2 * n → (∀ x ∈ ws, x ≠ []) →
    ∀ D : List (Fin (a + 4)),
    run splitProgram (flat (wordRecs (a := a) ws)).length
        (cfg (putWord (fun _ => blank) 0 (D ++ flat (pairs (a := a) ws))) D.length 0) =
      some (cfg (putWord (fun _ => blank) 0 (D ++ flat (wordRecs (a := a) ws)))
        (D.length + (flat (wordRecs (a := a) ws)).length) 0) := by
  induction n with
  | zero =>
    intro ws hl _ D
    obtain rfl : ws = [] := List.length_eq_zero_iff.mp (by omega)
    simp [wordRecs, pairs, flat_nil, run]
  | succ n ih =>
    intro ws hl hne D
    obtain ⟨x, y, rest, rfl⟩ : ∃ x y rest, ws = x :: y :: rest := by
      match ws, hl with
      | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
    obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
    obtain ⟨c, ys, rfl⟩ := List.exists_cons_of_ne_nil (hne y (by simp))
    have hrl : rest.length = 2 * n := by simp at hl; omega
    rw [flat_two, pairs_two]
    have hlen : ((b :: xs).map bitSymbol ++ blank :: ((c :: ys).map bitSymbol ++ blank :: flat (wordRecs (a := a) rest))).length =
        (1 + (xs.length + (1 + (1 + (ys.length + 1))))) + (flat (wordRecs (a := a) rest)).length := by simp; ring
    rw [hlen, run_add, List.map_cons, List.map_cons, List.cons_append, List.cons_append, split_pair_run]
    simp only [Option.bind_some]
    have e1 : D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ blank :: flat (pairs (a := a) rest)))) =
        (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ [blank])))) ++
          flat (pairs (a := a) rest) := by simp
    have hl1 : D.length + (1 + (xs.length + (1 + (1 + (ys.length + 1))))) =
        (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ [blank])))).length := by
      simp; ring
    have key := ih rest hrl (fun z hz => hne z (by simp [hz]))
      (D ++ bitSymbol b :: (xs.map bitSymbol ++ blank :: (bitSymbol c :: (ys.map bitSymbol ++ [blank]))))
    rw [e1]
    convert key using 3
    · rw [← hl1]; push_cast; ring
    · simp
    · simp; ring

/-- The split contract: `n` joined records become the word records of `2n` words. -/
theorem split_hoare (n : ℕ) (ws : List (List Bool)) (hl : ws.length = 2 * n) (hne : ∀ x ∈ ws, x ≠ []) :
    HoareTime (splitProgram (a := a)) (fun v => v = (cfg (inTape (pairs (a := a) ws)) 0 (0 : Fin 2)).tapes)
      (fun v => v = (cfg (inTape (wordRecs (a := a) ws)) (flat (wordRecs (a := a) ws)).length (0 : Fin 2)).tapes)
      (flat (wordRecs (a := a) ws)).length := by
  rintro v rfl
  have h := split_run (a := a) n ws hl hne []
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at h
  refine ⟨_, _, le_rfl, h, ?_, rfl⟩
  unfold step
  have hb : putWord (fun _ => (blank : Fin (a + 4))) 0 (flat (wordRecs (a := a) ws))
      ((flat (wordRecs (a := a) ws)).length : ℤ) = blank := by
    rw [pw_get]; simp
  simp [cfg, splitProgram, hb]

end Split

end IntegerMultBounds.Machine.PairJoin
