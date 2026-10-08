import IntegerMultBounds.Machine.BinaryPad

/-! Literal least-significant-first binary comparison. Three tapes and four
states: the two operands are scanned forward together, with a missing high
bit read as zero, and the order so far lives in finite control, a later
column overriding every earlier one. On the common blank the result bit,
whether the first operand is strictly smaller, is written on the third tape.
Both operands are preserved; the cost is the larger width plus one. -/

namespace IntegerMultBounds.Machine.BinaryCompare

variable {a : ℕ}

open BinaryPad (columns inputSymbol outputBit padded)

/-- The order after one more, more significant, column. -/
def cmpBit (o : Ordering) (x y : Bool) : Ordering :=
  if x = y then o else if x then .gt else .lt

/-- The order of two words from an initial order, least significant column first. -/
def rel : Ordering → List (Bool × Bool) → Ordering
  | o, [] => o
  | o, (x, y) :: rest => rel (cmpBit o x y) rest

theorem rel_eq (o : Ordering) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    rel o (xs.zip ys) = if Counter.value xs < Counter.value ys then .lt
      else if Counter.value ys < Counter.value xs then .gt else o := by
  induction xs generalizing ys o with
  | nil =>
    have hy : ys = [] := by simpa using hlen.symm
    subst ys
    simp [rel, Counter.value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hlen
      simp only [List.zip_cons_cons, rel, ih _ _ ht]
      cases x <;> cases y <;> simp only [cmpBit, Counter.value, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte] <;>
        split_ifs <;> first | rfl | omega

theorem rel_lt (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (rel .eq (xs.zip ys) = .lt) = (Counter.value xs < Counter.value ys) := by
  rw [rel_eq _ _ _ hlen]
  split_ifs <;> simp <;> omega

/-- The finite control: zero for equal so far, one for smaller, two for
larger, three after writing the result. -/
def ordState : Ordering → Fin 4
  | .eq => 0
  | .lt => 1
  | .gt => 2

def stateOrd (s : Fin 4) : Ordering := if s = 0 then .eq else if s = 1 then .lt else .gt

/-- A source cell is blank or a bit; blank reads as zero. -/
def isInput (x : Fin (a + 4)) : Prop := x = blank ∨ x = bitSymbol false ∨ x = bitSymbol true

instance (x : Fin (a + 4)) : Decidable (isInput x) := by unfold isInput; infer_instance

def program (a : ℕ) : Program 3 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 3 then none
    else if symbols 0 = blank ∧ symbols 1 = blank then
      some (3, fun i => if i = 2 then (bitSymbol (decide (state = 1)), .right) else (symbols i, .stay))
    else if isInput (symbols 0) ∧ isInput (symbols 1) then
      let x := decide (symbols 0 = bitSymbol true)
      let y := decide (symbols 1 = bitSymbol true)
      some (ordState (cmpBit (stateOrd state) x y), fun i => (symbols i, if i = 2 then .stay else .right))
    else none

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin 4) : Config 3 4 a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

private theorem column_step (o : Ordering) (x y : Option Bool) (hv : x ≠ none ∨ y ≠ none)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = inputSymbol y) :
    step (program a) (cfg f g out p q r (ordState o)) =
      some (cfg f g out (p + 1) (q + 1) r (ordState (cmpBit o (outputBit x) (outputBit y)))) := by
  have ht : (program a).transition (ordState o)
      (fun i => (cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i)) =
      some (ordState (cmpBit o (outputBit x) (outputBit y)), fun i =>
        ((cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i),
          if i = 2 then Move.stay else Move.right)) := by
    cases o <;> rcases x with _ | x <;> rcases y with _ | y <;> simp at hv <;>
      (try cases x) <;> (try cases y) <;>
      simp [program, cfg, ordState, stateOrd, cmpBit, isInput, hx, hy, inputSymbol, outputBit,
        blank, bitSymbol]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

/-- One transition per aligned column; every cell of all three tapes is retained. -/
theorem columns_run (o : Ordering) (cols : List (Option Bool × Option Bool))
    (hv : ∀ c ∈ cols, c.1 ≠ none ∨ c.2 ≠ none)
    (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    run (program a) cols.length
      (cfg (putWord f p (cols.map (fun c => inputSymbol c.1)))
        (putWord g q (cols.map (fun c => inputSymbol c.2))) out p q r (ordState o)) =
      some (cfg (putWord f p (cols.map (fun c => inputSymbol c.1)))
        (putWord g q (cols.map (fun c => inputSymbol c.2))) out
        (p + cols.length) (q + cols.length) r
        (ordState (rel o (cols.map (fun c => (outputBit c.1, outputBit c.2)))))) := by
  induction cols generalizing o f g p q with
  | nil => simp [run, putWord, rel]
  | cons col cols ih =>
    rcases col with ⟨x, y⟩
    have hs := column_step o x y (hv (x, y) (by simp))
      (putWord f p (((x, y) :: cols).map (fun c => inputSymbol c.1)))
      (putWord g q (((x, y) :: cols).map (fun c => inputSymbol c.2))) out p q r
      (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
    simp only [List.length_cons, run, hs, Option.bind_some]
    simp only [List.map_cons, putWord_cons]
    have hr := ih (cmpBit o (outputBit x) (outputBit y)) (fun c hc => hv c (by simp [hc]))
      (Function.update f p (inputSymbol x)) (Function.update g q (inputSymbol y)) (p + 1) (q + 1)
    simpa only [rel, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

private theorem final_step (o : Ordering) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : f p = blank) (hg : g q = blank) :
    step (program a) (cfg f g out p q r (ordState o)) =
      some (cfg f g (Function.update out r (bitSymbol (decide (o = .lt)))) p q (r + 1) 3) := by
  have ht : (program a).transition (ordState o)
      (fun i => (cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i)) =
      some (3, fun i => if i = 2 then (bitSymbol (decide (o = .lt)), Move.right)
        else ((cfg f g out p q r (ordState o)).tape i ((cfg f g out p q r (ordState o)).head i),
          Move.stay)) := by
    cases o <;> simp [program, cfg, ordState, hf, hg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

theorem halt (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    step (program a) (cfg f g out p q r 3) = none := by
  simp [step, program, cfg]

/-- Blank cells beyond a word may be absorbed into the written word. -/
theorem putWord_blank_tail (f : ℤ → Fin (a + 4)) (p : ℤ) (n : ℕ)
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

/-- The common width of two operands. -/
def width (xs ys : List Bool) : ℕ := max xs.length ys.length

/-- The result word: one bit, whether the first operand is strictly smaller. -/
def resultWord (xs ys : List Bool) : List (Fin (a + 4)) :=
  [bitSymbol (decide (Counter.value xs < Counter.value ys))]

/-- Exact execution: scan to the common width, write the result bit, halt. -/
theorem compare_exact (xs ys : List Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs ys → f (p + j) = blank)
    (hg : ∀ j : ℕ, ys.length ≤ j → j ≤ width xs ys → g (q + j) = blank) :
    run (program a) (width xs ys + 1)
      (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out p q r 0) =
      some (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + width xs ys) (q + width xs ys) (r + 1) 3) ∧
    step (program a) (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + width xs ys) (q + width xs ys) (r + 1) 3) = none := by
  refine ⟨?_, halt _ _ _ _ _ _⟩
  simp only [width] at hf hg ⊢
  have hfx : putWord f p (xs.map bitSymbol) =
      putWord f p ((columns xs ys).map (fun c => inputSymbol c.1)) := by
    rw [BinaryPad.columns_left_input, putWord_append, putWord_blank_tail]
    intro j hj
    rw [show p + (xs.map (bitSymbol (a := a))).length + (j : ℤ) = p + ((xs.length + j : ℕ) : ℤ) by
      push_cast; simp; ring]
    exact hf _ (by omega) (by omega)
  have hgy : putWord g q (ys.map bitSymbol) =
      putWord g q ((columns xs ys).map (fun c => inputSymbol c.2)) := by
    rw [BinaryPad.columns_right_input, putWord_append, putWord_blank_tail]
    intro j hj
    rw [show q + (ys.map (bitSymbol (a := a))).length + (j : ℤ) = q + ((ys.length + j : ℕ) : ℤ) by
      push_cast; simp; ring]
    exact hg _ (by omega) (by omega)
  have hr := columns_run .eq (columns xs ys) (BinaryPad.columns_valid xs ys) f g out p q r
  have hw : (columns xs ys).length = max xs.length ys.length := BinaryPad.columns_length xs ys
  have hrel : rel .eq ((columns xs ys).map (fun c => (outputBit c.1, outputBit c.2))) =
      rel .eq ((padded xs (max xs.length ys.length)).zip (padded ys (max xs.length ys.length))) := by
    rw [← BinaryPad.columns_left_output, ← BinaryPad.columns_right_output, List.zip_map']
  have hlt : rel .eq ((padded xs (max xs.length ys.length)).zip
      (padded ys (max xs.length ys.length))) = .lt ↔
      Counter.value xs < Counter.value ys := by
    rw [← BinaryPad.padded_value xs (max xs.length ys.length),
      ← BinaryPad.padded_value ys (max xs.length ys.length)]
    exact iff_of_eq (rel_lt _ _ (by
      rw [BinaryPad.padded_length _ _ (Nat.le_max_left _ _),
        BinaryPad.padded_length _ _ (Nat.le_max_right _ _)]))
  have hblankf : putWord f p ((columns xs ys).map (fun c => inputSymbol c.1))
      (p + (columns xs ys).length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hw]
    exact hf _ (Nat.le_max_left _ _) le_rfl
  have hblankg : putWord g q ((columns xs ys).map (fun c => inputSymbol c.2))
      (q + (columns xs ys).length) = blank := by
    rw [putWord_outside _ _ (q + (columns xs ys).length) _ (Or.inr (by simp)), hw]
    exact hg _ (Nat.le_max_right _ _) le_rfl
  have hfin := final_step (rel .eq ((columns xs ys).map (fun c => (outputBit c.1, outputBit c.2))))
    (putWord f p ((columns xs ys).map (fun c => inputSymbol c.1)))
    (putWord g q ((columns xs ys).map (fun c => inputSymbol c.2))) out
    (p + (columns xs ys).length) (q + (columns xs ys).length) r hblankf hblankg
  have hbit : (decide (rel .eq ((columns xs ys).map (fun c => (outputBit c.1, outputBit c.2))) = .lt)) =
      decide (Counter.value xs < Counter.value ys) := by
    rw [hrel]; exact decide_eq_decide.mpr hlt
  rw [hfx, hgy, run_add, ← hw, show ordState .eq = 0 from rfl] at *
  rw [hr]
  simp only [Option.bind_some, run_one, hfin, hbit, resultWord, putWord]

/-- The comparison contract: both operands are preserved, the result bit is
written at the output head, and the heads advance to the common width. -/
theorem compare_hoare (xs ys : List Bool) (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (hf : ∀ j : ℕ, xs.length ≤ j → j ≤ width xs ys → f (p + j) = blank)
    (hg : ∀ j : ℕ, ys.length ≤ j → j ≤ width xs ys → g (q + j) = blank) :
    HoareTime (program a)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out
        p q r 0).tapes)
      (fun v => v = (cfg (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r (resultWord xs ys)) (p + width xs ys) (q + width xs ys) (r + 1) 0).tapes)
      (width xs ys + 1) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := compare_exact xs ys f g out p q r hf hg
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.BinaryCompare
