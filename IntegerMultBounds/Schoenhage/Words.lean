import IntegerMultBounds.Machine.WordTape

/-! Tapes holding lists of binary words. A word is written as its bits
followed by one separator; the words of a tape are laid out from cell zero,
blank everywhere else. The abstract tape is a zipper: the words left of the
head (nearest first) and the words from the head on. The head sits on the
first cell of the first right word, or on the blank after the last word. -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a : ℕ}

/-- A tape symbol: a bit, or the separator (`none`). -/
def sym : Option Bool → Fin (a + 4)
  | none => separator
  | some b => bitSymbol b

theorem sym_ne_blank (o : Option Bool) : sym (a := a) o ≠ blank := by
  cases o with
  | none => simp [sym, separator, blank]
  | some b => cases b <;> simp [sym, bitSymbol, blank]

theorem sym_injective : Function.Injective (sym (a := a)) := by
  intro x y h
  rcases x with _ | ⟨_ | _⟩ <;> rcases y with _ | ⟨_ | _⟩ <;>
    simp_all [sym, separator, bitSymbol, Fin.ext_iff]

/-- The symbols of a word list. -/
def syms (ws : List (List Bool)) : List (Option Bool) := ws.flatMap fun w => w.map some ++ [none]

@[simp] theorem syms_nil : syms [] = [] := rfl

@[simp] theorem syms_cons (w : List Bool) (ws : List (List Bool)) :
    syms (w :: ws) = w.map some ++ [none] ++ syms ws := by simp [syms]

theorem syms_append (ws vs : List (List Bool)) : syms (ws ++ vs) = syms ws ++ syms vs := by
  simp [syms]

/-- Total cell length of a word list. -/
def clen (ws : List (List Bool)) : ℕ := (ws.map fun w => w.length + 1).sum

@[simp] theorem clen_nil : clen [] = 0 := rfl

@[simp] theorem clen_cons (w : List Bool) (ws : List (List Bool)) :
    clen (w :: ws) = w.length + 1 + clen ws := by simp [clen]

theorem clen_append (ws vs : List (List Bool)) : clen (ws ++ vs) = clen ws + clen vs := by
  simp [clen]

theorem clen_reverse (ws : List (List Bool)) : clen ws.reverse = clen ws := by
  simp [clen, List.sum_reverse]

theorem length_syms (ws : List (List Bool)) : (syms ws).length = clen ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ih]; ring

/-- The cells of a word list. -/
def cells (ws : List (List Bool)) : List (Fin (a + 4)) := (syms ws).map sym

theorem length_cells (ws : List (List Bool)) : (cells (a := a) ws).length = clen ws := by
  simp [cells, length_syms]

/-- An abstract tape of words with the head at a word boundary. -/
structure WTape where
  left : List (List Bool)
  right : List (List Bool)

namespace WTape

/-- All words in tape order. -/
def words (T : WTape) : List (List Bool) := T.left.reverse ++ T.right

/-- The head cell. -/
def pos (T : WTape) : ℤ := clen T.left

/-- The physical tape. -/
def tape (T : WTape) : ℤ → Fin (a + 4) := wordTape (cells T.words)

theorem tape_eq (T : WTape) (j : ℤ) :
    T.tape (a := a) j = if 0 ≤ j then ((syms T.words)[j.toNat]?.map sym).getD blank else blank := by
  simp only [tape, wordTape, cells, List.getElem?_map]

/-- Reading the symbols from the head on. -/
theorem tape_at_pos (T : WTape) (c : ℕ) :
    T.tape (a := a) (T.pos + c) = ((syms T.right)[c]?.map sym).getD blank := by
  rw [tape_eq, if_pos (by unfold pos; omega)]
  have h : (T.pos + c).toNat = clen T.left.reverse + c := by
    unfold pos; rw [clen_reverse]; omega
  rw [h, words, syms_append, ← length_syms, List.getElem?_append_right (by omega)]
  simp

theorem tape_word (T : WTape) {w : List Bool} {R : List (List Bool)} (h : T.right = w :: R)
    (c : ℕ) (hc : c < w.length) : T.tape (a := a) (T.pos + c) = bitSymbol w[c] := by
  rw [tape_at_pos, h, syms_cons, List.append_assoc, List.getElem?_append_left (by simpa using hc)]
  simp [sym, hc]

theorem tape_sep (T : WTape) {w : List Bool} {R : List (List Bool)} (h : T.right = w :: R) :
    T.tape (a := a) (T.pos + w.length) = separator := by
  rw [tape_at_pos, h, syms_cons, List.append_assoc, List.getElem?_append_right (by simp)]
  simp [sym]

theorem tape_end (T : WTape) (h : T.right = []) (c : ℕ) :
    T.tape (a := a) (T.pos + c) = blank := by
  rw [tape_at_pos, h]; simp

theorem tape_neg (T : WTape) (j : ℤ) (h : j < 0) : T.tape (a := a) j = blank := by
  rw [tape_eq, if_neg (by omega)]

theorem update_wordTape (A : List (Fin (a + 4))) (x : Fin (a + 4)) :
    Function.update (wordTape A) (A.length : ℤ) x = wordTape (A ++ [x]) := by
  funext j
  by_cases hj : j = A.length
  · subst hj; simp [wordTape]
  · rw [Function.update_of_ne hj]
    unfold wordTape
    split_ifs with h0
    · rcases lt_or_gt_of_ne (show j.toNat ≠ A.length by omega) with hl | hl
      · rw [List.getElem?_append_left hl]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · rfl

theorem put_wordTape (A B : List (Fin (a + 4))) :
    putWord (wordTape A) (A.length : ℤ) B = wordTape (A ++ B) := by
  induction B generalizing A with
  | nil => simp [putWord]
  | cons x B ih =>
    rw [putWord_cons, update_wordTape, show (A.length : ℤ) + 1 = ((A ++ [x]).length : ℤ) by simp,
      ih]
    simp

/-- Writing word symbols at the end of a tape. -/
theorem put_end (T : WTape) (h : T.right = []) (vs : List (List Bool)) :
    putWord (T.tape (a := a)) T.pos (cells vs) = (⟨vs.reverse ++ T.left, []⟩ : WTape).tape := by
  have hp : T.pos = ((cells (a := a) T.left.reverse).length : ℤ) := by
    rw [length_cells, clen_reverse]; rfl
  simp only [tape, words, h, List.append_nil, List.reverse_append, List.reverse_reverse]
  rw [hp, put_wordTape]
  simp [cells, syms_append]

end WTape

end IntegerMultBounds.Schoenhage
