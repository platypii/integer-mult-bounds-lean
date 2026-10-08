import IntegerMultBounds.Machine.WordTape
import IntegerMultBounds.Machine.Hoare
import IntegerMultBounds.Machine.Counter

/-! Literal two-tape preparation of equally padded LSF operands. Missing
high bits become zero, at one transition per column of the longer operand. -/

namespace IntegerMultBounds.Machine.BinaryPad

variable {a : ℕ}

def columns : List Bool → List Bool → List (Option Bool × Option Bool)
  | [], ys => ys.map (fun y => (none, some y))
  | xs, [] => xs.map (fun x => (some x, none))
  | x :: xs, y :: ys => (some x, some y) :: columns xs ys

def padded (xs : List Bool) (width : ℕ) : List Bool :=
  xs ++ List.replicate (width - xs.length) false

def inputSymbol : Option Bool → Fin (a + 4)
  | none => blank
  | some b => bitSymbol b

def outputBit (x : Option Bool) : Bool := x.getD false

@[simp] theorem columns_length (xs ys : List Bool) :
    (columns xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [columns]
  | cons x xs ih => cases ys <;> simp [columns, ih, max_add_add_right]

theorem columns_valid (xs ys : List Bool) :
    ∀ c ∈ columns xs ys, c.1 ≠ none ∨ c.2 ≠ none := by
  induction xs generalizing ys with
  | nil =>
    intro c hc
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hc
    simp
  | cons x xs ih =>
    cases ys with
    | nil =>
      intro c hc
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hc
      simp
    | cons y ys =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · exact ih ys c hc

theorem columns_left_input (xs ys : List Bool) :
    (columns xs ys).map (fun c => inputSymbol (a := a) c.1) =
      xs.map bitSymbol ++ List.replicate (max xs.length ys.length - xs.length) blank := by
  induction xs generalizing ys with
  | nil => simp [columns, inputSymbol, Function.comp_def]
  | cons x xs ih =>
    cases ys with
    | nil => simp [columns, inputSymbol, Function.comp_def]
    | cons y ys => simpa only [columns, List.map_cons, inputSymbol, List.length_cons,
        max_add_add_right, Nat.add_sub_add_right, List.cons_append] using congrArg (List.cons (bitSymbol x)) (ih ys)

theorem columns_right_input (xs ys : List Bool) :
    (columns xs ys).map (fun c => inputSymbol (a := a) c.2) =
      ys.map bitSymbol ++ List.replicate (max xs.length ys.length - ys.length) blank := by
  induction xs generalizing ys with
  | nil => simp [columns, inputSymbol, Function.comp_def]
  | cons x xs ih =>
    cases ys with
    | nil => simp [columns, inputSymbol, Function.comp_def, List.replicate_succ]
    | cons y ys => simpa only [columns, List.map_cons, inputSymbol, List.length_cons,
        max_add_add_right, Nat.add_sub_add_right, List.cons_append] using congrArg (List.cons (bitSymbol y)) (ih ys)

theorem columns_left_output (xs ys : List Bool) :
    (columns xs ys).map (fun c => outputBit c.1) = padded xs (max xs.length ys.length) := by
  induction xs generalizing ys with
  | nil => simp [columns, padded, outputBit, Function.comp_def]
  | cons x xs ih =>
    cases ys with
    | nil => simp [columns, padded, outputBit, Function.comp_def]
    | cons y ys => simpa only [columns, List.map_cons, outputBit, Option.getD_some, List.length_cons,
        max_add_add_right, padded, Nat.add_sub_add_right, List.cons_append] using congrArg (List.cons x) (ih ys)

theorem columns_right_output (xs ys : List Bool) :
    (columns xs ys).map (fun c => outputBit c.2) = padded ys (max xs.length ys.length) := by
  induction xs generalizing ys with
  | nil => simp [columns, padded, outputBit, Function.comp_def]
  | cons x xs ih =>
    cases ys with
    | nil => simp [columns, padded, outputBit, Function.comp_def, List.replicate_succ]
    | cons y ys => simpa only [columns, List.map_cons, outputBit, Option.getD_some, List.length_cons,
        max_add_add_right, padded, Nat.add_sub_add_right, List.cons_append] using congrArg (List.cons y) (ih ys)

theorem padded_length (xs : List Bool) (width : ℕ) (h : xs.length ≤ width) :
    (padded xs width).length = width := by simp [padded]; omega

theorem padded_value (xs : List Bool) (width : ℕ) :
    Counter.value (padded xs width) = Counter.value xs := by
  have hz (n : ℕ) : Counter.value (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, Counter.value, ih]
  have ha (xs : List Bool) (n : ℕ) :
      Counter.value (xs ++ List.replicate n false) = Counter.value xs := by
    induction xs with
    | nil => simpa [Counter.value] using hz n
    | cons b xs ih => simp [Counter.value, ih]
  exact ha xs _

def program (a : ℕ) : Program 2 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols =>
    if symbols 0 = blank ∧ symbols 1 = blank then none
    else some (0, fun i => (if symbols i = blank then bitSymbol false else symbols i, .right))

def cfg (f g : ℤ → Fin (a + 4)) (p q : ℤ) : Config 2 1 a where
  state := 0
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else g

private theorem column_step (x y : Option Bool) (hv : x ≠ none ∨ y ≠ none)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ)
    (hx : f p = inputSymbol x) (hy : g q = inputSymbol y) :
    step (program a) (cfg f g p q) =
      some (cfg (Function.update f p (bitSymbol (outputBit x)))
        (Function.update g q (bitSymbol (outputBit y))) (p + 1) (q + 1)) := by
  have ht : (program a).transition 0 (fun i => (cfg f g p q).tape i ((cfg f g p q).head i)) =
      some (0, fun i => (if i = 0 then bitSymbol (outputBit x) else bitSymbol (outputBit y), Move.right)) := by
    cases x with
    | none =>
      cases y with
      | none => simp at hv
      | some y => cases y <;> simp [program, cfg, hx, hy, inputSymbol, outputBit, blank, bitSymbol] <;>
          (funext i; fin_cases i <;> simp [hx, hy, inputSymbol, blank, bitSymbol])
    | some x =>
      cases y with
      | none => cases x <;> simp [program, cfg, hx, hy, inputSymbol, outputBit, blank, bitSymbol] <;>
          (funext i; fin_cases i <;> simp [hx, hy, inputSymbol, blank, bitSymbol])
      | some y => cases x <;> cases y <;> simp [program, cfg, hx, hy, inputSymbol, outputBit, blank, bitSymbol] <;>
          (funext i; fin_cases i <;> simp [hx, hy, inputSymbol, bitSymbol])
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j; fin_cases i <;> simp [Function.update_apply, eq_comm]

/-- A literal transition for each aligned column, preserving all cells outside
the two finite segments, including arbitrary earlier tape contents. -/
theorem columns_run (cols : List (Option Bool × Option Bool))
    (hv : ∀ c ∈ cols, c.1 ≠ none ∨ c.2 ≠ none)
    (f g : ℤ → Fin (a + 4)) (p q : ℤ) :
    run (program a) cols.length
      (cfg (putWord f p (cols.map (fun c => inputSymbol c.1)))
        (putWord g q (cols.map (fun c => inputSymbol c.2))) p q) =
      some (cfg (putWord f p (cols.map (fun c => bitSymbol (outputBit c.1))))
        (putWord g q (cols.map (fun c => bitSymbol (outputBit c.2))))
        (p + cols.length) (q + cols.length)) := by
  induction cols generalizing f g p q with
  | nil => simp [run, putWord]
  | cons col cols ih =>
    rcases col with ⟨x, y⟩
    have hs := column_step x y (hv (x, y) (by simp))
      (putWord f p (((x, y) :: cols).map (fun c => inputSymbol c.1)))
      (putWord g q (((x, y) :: cols).map (fun c => inputSymbol c.2))) p q
      (by rw [List.map_cons, putWord_head]) (by rw [List.map_cons, putWord_head])
    simp only [List.length_cons, run, hs, Option.bind_some]
    simp only [List.map_cons, putWord_replace_head]
    have hr := ih (fun c hc => hv c (by simp [hc]))
      (Function.update f p (bitSymbol (outputBit x)))
      (Function.update g q (bitSymbol (outputBit y))) (p + 1) (q + 1)
    simpa only [← putWord_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

private theorem blank_replicate (n : ℕ) (p : ℤ) :
    putWord (fun _ => (blank : Fin (a + 4))) p (List.replicate n blank) = (fun _ => blank) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, putWord, ih]

private theorem input_word (xs : List Bool) (n : ℕ) :
    putWord (fun _ => (blank : Fin (a + 4))) 0 (xs.map bitSymbol ++ List.replicate n blank) =
      wordTape (xs.map bitSymbol) := by
  rw [putWord_append, blank_replicate]
  funext j
  simpa using putWord_blank 0 j (xs.map bitSymbol)

/-- The whole-tape padding contract. Both heads end at the common maximum
width and the machine really halts there, with blank tails on both tapes. -/
theorem pad_exact (xs ys : List Bool) :
    let width := max xs.length ys.length
    run (program a) width (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) 0 0) =
      some (cfg (wordTape ((padded xs width).map bitSymbol))
        (wordTape ((padded ys width).map bitSymbol)) width width) ∧
    step (program a) (cfg (wordTape ((padded xs width).map bitSymbol))
      (wordTape ((padded ys width).map bitSymbol)) width width) = none := by
  dsimp only
  have hr := columns_run (columns xs ys) (columns_valid xs ys)
    (fun _ => (blank : Fin (a + 4))) (fun _ => blank) 0 0
  have ho (bits : List Bool) : putWord (fun _ => (blank : Fin (a + 4))) 0 (bits.map bitSymbol) =
      wordTape (bits.map bitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (bits.map bitSymbol)
  have hl : (columns xs ys).map (fun c => bitSymbol (a := a) (outputBit c.1)) =
      (padded xs (max xs.length ys.length)).map bitSymbol := by
    rw [← columns_left_output, List.map_map]; rfl
  have hh : (columns xs ys).map (fun c => bitSymbol (a := a) (outputBit c.2)) =
      (padded ys (max xs.length ys.length)).map bitSymbol := by
    rw [← columns_right_output, List.map_map]; rfl
  constructor
  · simpa only [columns_length, columns_left_input, columns_right_input, input_word, hl, hh,
      ho, zero_add] using hr
  · simp [step, program, cfg, wordTape, padded_length _ _ (Nat.le_max_left _ _),
      padded_length _ _ (Nat.le_max_right _ _)]

/-- Equal-width preparation with exact values, complete blank-tail tapes,
and a maximum-width transition bound. Rewinding is a separate operation. -/
theorem pad_hoare (xs ys : List Bool) :
    HoareTime (program a)
      (fun v => v = (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) 0 0).tapes)
      (fun v => ∃ px py : List Bool,
        Counter.value px = Counter.value xs ∧ Counter.value py = Counter.value ys ∧
        px.length = max xs.length ys.length ∧ py.length = max xs.length ys.length ∧
        v = (cfg (wordTape (px.map bitSymbol)) (wordTape (py.map bitSymbol))
          (max xs.length ys.length) (max xs.length ys.length)).tapes)
      (max xs.length ys.length) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := pad_exact (a := a) xs ys
  exact ⟨_, _, le_rfl, hr, hh, padded xs _, padded ys _, padded_value _ _, padded_value _ _,
    padded_length _ _ (Nat.le_max_left _ _), padded_length _ _ (Nat.le_max_right _ _), by simp⟩

end IntegerMultBounds.Machine.BinaryPad
