import IntegerMultBounds.Machine.Copy

/-! A stable three-tape partition of delimiter-separated records by their first
bit. The source is preserved; each record is appended to the selected output.
The control has three states independently of record widths and stream length.
This is a routing pass, not yet an implementation of full radix sorting. -/

namespace IntegerMultBounds.Machine.Partition

def phase (b : Bool) : Fin 3 := if b then 2 else 1

def emit (b : Bool) (next : Fin 3) (symbols : Fin 3 → Fin 4) :
    Fin 3 × (Fin 3 → Fin 4 × Move) :=
  (next, fun i => if i = 0 ∨ i = phase b then (symbols 0, .right)
    else (symbols i, .stay))

/-- State zero reads a record key; states one and two remember its bucket. -/
def program : Program 3 3 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 0 = bitSymbol false then some (emit false (phase false) symbols)
      else if symbols 0 = bitSymbol true then some (emit true (phase true) symbols)
      else none
    else
      let b := decide (s = 2)
      some (emit b (if symbols 0 = separator then 0 else phase b) symbols)

/-- In this view, `g` is the selected output and `h` is the other output. -/
def cfg (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ) (s : Fin 3) : Config 3 3 0 where
  state := s
  head := fun i => if i = 0 then p else if i = phase b then q else r
  tape := fun i => if i = 0 then f else if i = phase b then g else h

theorem cfg_true (f g h : ℤ → Fin 4) (p q r : ℤ) (s : Fin 3) :
    cfg true f g h p q r s = cfg false f h g p r q s := by
  unfold cfg
  congr 1
  · funext i; fin_cases i <;> simp [phase]
  · funext i; fin_cases i <;> simp [phase]

private theorem emit_step (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ) (s next : Fin 3)
    (ht : program.transition s (fun i => (cfg b f g h p q r s).tape i
        ((cfg b f g h p q r s).head i)) =
      some (emit b next (fun i => (cfg b f g h p q r s).tape i
        ((cfg b f g h p q r s).head i)))) :
    step program (cfg b f g h p q r s) =
      some (cfg b f (Function.update g q (f p)) h (p + 1) (q + 1) r next) := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [emit]
  congr 1
  congr 1
  · funext i
    cases b <;> fin_cases i <;> simp [phase, Move.offset]
  · funext i j
    cases b <;> fin_cases i <;> simp [phase, Function.update_apply, eq_comm] <;>
      intro hj <;> rw [hj]

theorem key_step (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ)
    (hk : f p = bitSymbol b) :
    step program (cfg b f g h p q r 0) =
      some (cfg b f (Function.update g q (bitSymbol b)) h (p + 1) (q + 1) r (phase b)) := by
  rw [← hk]
  apply emit_step
  cases b <;> simp [program, cfg, phase, hk, bitSymbol]

theorem body_step (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p ≠ separator) :
    step program (cfg b f g h p q r (phase b)) =
      some (cfg b f (Function.update g q (f p)) h (p + 1) (q + 1) r (phase b)) := by
  apply emit_step
  cases b <;> simp [program, cfg, phase, hx]

theorem delimiter_step (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p = separator) :
    step program (cfg b f g h p q r (phase b)) =
      some (cfg b f (Function.update g q separator) h (p + 1) (q + 1) r 0) := by
  rw [← hx]
  apply emit_step
  cases b <;> simp [program, cfg, phase, hx]

theorem halt (f g h : ℤ → Fin 4) (p q r : ℤ) (hx : f p = blank) :
    step program (cfg false f g h p q r 0) = none := by
  simp [step, program, cfg, hx, blank, bitSymbol]

/-- Copy the rest of one record, including its terminating delimiter. -/
theorem body_run (b : Bool) (f g h : ℤ → Fin 4) (p q r : ℤ) (xs : List (Fin 4))
    (hxs : ∀ x ∈ xs, x ≠ separator) :
    run program (xs.length + 1)
      (cfg b (putWord f p (xs ++ [separator])) g h p q r (phase b)) =
      some (cfg b (putWord f p (xs ++ [separator]))
        (putWord g q (xs ++ [separator])) h
        (p + (xs.length + 1)) (q + (xs.length + 1)) r 0) := by
  induction xs generalizing f g p q with
  | nil =>
    simpa only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add, run_one,
      putWord] using delimiter_step b (Function.update f p separator) g h p q r (by simp)
  | cons x xs ih =>
    have hs := body_step b (putWord f p ((x :: xs) ++ [separator])) g h p q r
      (by rw [List.cons_append, putWord_head]; exact hxs x (by simp))
    rw [List.cons_append, putWord_head] at hs
    simp only [List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p x) (Function.update g q x) (p + 1) (q + 1)
      (fun y hy => hxs y (by simp [hy]))
    simpa only [← putWord_cons, List.cons_append, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm, add_left_comm] using hr

def recordWord (key : Bool) (payload : List Bool) : List (Fin 4) :=
  bitSymbol key :: (payload.map bitSymbol ++ [separator])

theorem record_run (b : Bool) (payload : List Bool) (f g h : ℤ → Fin 4) (p q r : ℤ) :
    run program (recordWord b payload).length
      (cfg b (putWord f p (recordWord b payload)) g h p q r 0) =
      some (cfg b (putWord f p (recordWord b payload)) (putWord g q (recordWord b payload)) h
        (p + (recordWord b payload).length) (q + (recordWord b payload).length) r 0) := by
  have hs := key_step b (putWord f p (recordWord b payload)) g h p q r
    (putWord_head f p _ _)
  simp only [recordWord] at hs
  simp only [recordWord, List.length_cons]
  rw [run, hs]
  simp only [Option.bind_some]
  have hr := body_run b (Function.update f p (bitSymbol b))
    (Function.update g q (bitSymbol b)) h (p + 1) (q + 1) r (payload.map bitSymbol)
    (by intro x hx; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; cases v <;> decide)
  simpa only [← putWord_cons, List.length_append, List.length_singleton,
    Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

structure Record where
  key : Bool
  payload : List Bool

def encode : List Record → List (Fin 4)
  | [] => []
  | rec :: rest => recordWord rec.key rec.payload ++ encode rest

def bucket (b : Bool) (records : List Record) : List (Fin 4) :=
  encode (records.filter (fun rec => rec.key == b))

@[simp] theorem bucket_nil (b : Bool) : bucket b [] = [] := rfl

@[simp] theorem bucket_cons (b key : Bool) (payload : List Bool) (rest : List Record) :
    bucket b (⟨key, payload⟩ :: rest) =
      if key = b then recordWord key payload ++ bucket b rest else bucket b rest := by
  cases key <;> cases b <;> simp [bucket, encode]

/-- The two output volumes sum to the input volume, including all delimiters. -/
theorem bucket_lengths (records : List Record) :
    (bucket false records).length + (bucket true records).length = (encode records).length := by
  induction records with
  | nil => rfl
  | cons rec rest ih =>
    rcases rec with ⟨key, payload⟩
    cases key <;> simp only [bucket_cons, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, List.length_append, encode] <;> omega

/-- Exact stable partition: both outputs are the original-order filtered record
streams. Source and all cells outside the written output segments are retained. -/
theorem stream_run (records : List Record) (f g h : ℤ → Fin 4) (p q r : ℤ) :
    run program (encode records).length (cfg false (putWord f p (encode records)) g h p q r 0) =
      some (cfg false (putWord f p (encode records))
        (putWord g q (bucket false records)) (putWord h r (bucket true records))
        (p + (encode records).length) (q + (bucket false records).length)
        (r + (bucket true records).length) 0) := by
  induction records generalizing f g h p q r with
  | nil => simp [encode, putWord, run]
  | cons rec rest ih =>
    rcases rec with ⟨key, payload⟩
    cases key with
    | false =>
      let w := recordWord false payload
      have hf := record_run false payload (putWord f (p + w.length) (encode rest)) g h p q r
      change run program w.length
        (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w) g h p q r 0) =
        some (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w)
          (putWord g q w) h (p + w.length) (q + w.length) r 0) at hf
      rw [← putWord_append] at hf
      have ht := ih (putWord f p w) (putWord g q w) h
        (p + w.length) (q + w.length) r
      simp only [putWord_append_forward] at ht
      simp only [encode, List.length_append, run_add]
      rw [hf]
      simp only [Option.bind_some]
      simpa only [bucket_cons, ↓reduceIte, Bool.false_eq_true, List.length_append,
        Nat.cast_add, add_assoc] using ht
    | true =>
      let w := recordWord true payload
      have hf := record_run true payload (putWord f (p + w.length) (encode rest)) h g p r q
      change run program w.length
        (cfg true (putWord (putWord f (p + w.length) (encode rest)) p w) h g p r q 0) =
        some (cfg true (putWord (putWord f (p + w.length) (encode rest)) p w)
          (putWord h r w) g (p + w.length) (r + w.length) q 0) at hf
      rw [← putWord_append] at hf
      simp only [cfg_true] at hf
      have ht := ih (putWord f p w) g (putWord h r w)
        (p + w.length) q (r + w.length)
      simp only [putWord_append_forward] at ht
      simp only [encode, List.length_append, run_add]
      rw [hf]
      simp only [Option.bind_some]
      simpa only [bucket_cons, ↓reduceIte, Bool.true_eq_false, List.length_append,
        Nat.cast_add, add_assoc] using ht

theorem recordWord_nonblank (key : Bool) (payload : List Bool) :
    ∀ x ∈ recordWord key payload, x ≠ blank := by
  intro x hx
  simp only [recordWord, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hbit | rfl
  · cases key <;> decide
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hbit
    cases b <;> decide
  · decide

theorem encode_nonblank (records : List Record) : ∀ x ∈ encode records, x ≠ blank := by
  induction records with
  | nil => simp [encode]
  | cons rec rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with hrec | hrest
    · exact recordWord_nonblank rec.key rec.payload x hrec
    · exact ih x hrest

theorem bucket_nonblank (b : Bool) (records : List Record) :
    ∀ x ∈ bucket b records, x ≠ blank := encode_nonblank _

/-- The complete pass halts at the source stream's blank terminator. -/
theorem stream_exact (records : List Record) (f g h : ℤ → Fin 4) (p q r : ℤ)
    (hend : f (p + (encode records).length) = blank) :
    run program (encode records).length (cfg false (putWord f p (encode records)) g h p q r 0) =
      some (cfg false (putWord f p (encode records))
        (putWord g q (bucket false records)) (putWord h r (bucket true records))
        (p + (encode records).length) (q + (bucket false records).length)
        (r + (bucket true records).length) 0) ∧
    step program (cfg false (putWord f p (encode records))
        (putWord g q (bucket false records)) (putWord h r (bucket true records))
        (p + (encode records).length) (q + (bucket false records).length)
        (r + (bucket true records).length) 0) = none := by
  refine ⟨stream_run records f g h p q r, halt _ _ _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr le_rfl), hend]

/-- On initially blank outputs, the two complete output tapes are exactly the
stable filtered streams, blank everywhere outside their encoded words. -/
theorem stream_blank (records : List Record) :
    run program (encode records).length
      (cfg false (wordTape (encode records)) (fun _ => blank) (fun _ => blank) 0 0 0 0) =
      some (cfg false (wordTape (encode records)) (wordTape (bucket false records))
        (wordTape (bucket true records)) (encode records).length
        (bucket false records).length (bucket true records).length 0) ∧
    step program (cfg false (wordTape (encode records)) (wordTape (bucket false records))
        (wordTape (bucket true records)) (encode records).length
        (bucket false records).length (bucket true records).length 0) = none := by
  have hw (xs : List (Fin 4)) : putWord (fun _ => blank) 0 xs = wordTape xs := by
    funext j
    simpa using putWord_blank 0 j xs
  simpa only [hw, zero_add] using
    stream_exact records (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 rfl

/-- A compositional contract retaining the complete input and both output tapes. -/
theorem stream_hoare (records : List Record) (f g h : ℤ → Fin 4) (p q r : ℤ)
    (hend : f (p + (encode records).length) = blank) :
    HoareTime program
      (fun v => v = (cfg false (putWord f p (encode records)) g h p q r 0).tapes)
      (fun v => v = (cfg false (putWord f p (encode records))
        (putWord g q (bucket false records)) (putWord h r (bucket true records))
        (p + (encode records).length) (q + (bucket false records).length)
        (r + (bucket true records).length) 0).tapes) (encode records).length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact records f g h p q r hend
  exact ⟨(encode records).length, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.Partition
