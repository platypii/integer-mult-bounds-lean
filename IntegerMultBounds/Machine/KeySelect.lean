import IntegerMultBounds.Machine.KeySelectData

/-! Select a key position from a unary tape, then prepend that bit to every
record while retaining its complete payload. The three-tape finite control is
independent of the index, record count, and record widths. Source and unary tape
are retained literally; rewinds are actual left-moving transitions. -/

namespace IntegerMultBounds.Machine.KeySelect

def remember (b : Bool) : Fin 4 := if b then 2 else 1

private def action (symbols : Fin 3 → Fin 5) (sm um om : Move) (out : Fin 5) :
    Fin 3 → Fin 5 × Move :=
  fun i => (if i = 2 then out else symbols i,
    if i = 0 then sm else if i = 1 then um else om)

/-- State zero selects; states one/two rewind carrying the selected bit; state
three copies the entire record. Tape one is a unary index with a left marker. -/
def program : Program 3 4 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 0 = blank then none
      else if symbols 1 = blank then
        if symbols 0 = bitSymbol false then
          some (remember false, action symbols .left .left .stay (symbols 2))
        else if symbols 0 = bitSymbol true then
          some (remember true, action symbols .left .left .stay (symbols 2))
        else none
      else some (0, action symbols .right .right .stay (symbols 2))
    else if s = 3 then
      some ((if symbols 0 = separator then 0 else 3), action symbols .right .stay .right (symbols 0))
    else if symbols 1 = PartitionMarked.marker then
      some (3, action symbols .right .right .right (bitSymbol (decide (s = 2))))
    else some (s, action symbols .left .left .stay (symbols 2))

def cfg (f unary out : ℤ → Fin 5) (p u q : ℤ) (s : Fin 4) : Config 3 4 1 where
  state := s
  head := fun i => if i = 0 then p else if i = 1 then u else q
  tape := fun i => if i = 0 then f else if i = 1 then unary else out

/-- Index k is encoded by k unary symbols, blank terminator, and a left marker. -/
def selector (k : ℕ) (j : ℤ) : Fin 5 :=
  if j = -1 then PartitionMarked.marker
  else if 0 ≤ j ∧ j < k then bitSymbol true else blank

@[simp] theorem selector_left (k : ℕ) : selector k (-1) = PartitionMarked.marker := by
  simp [selector]

@[simp] theorem selector_end (k : ℕ) : selector k k = blank := by
  have hk : (k : ℤ) ≠ -1 := by omega
  simp [selector, hk]

theorem selector_inside (k j : ℕ) (h : j < k) : selector k j = bitSymbol true := by
  have hn : (j : ℤ) ≠ -1 := by omega
  have hj : (j : ℤ) < k := by omega
  simp [selector, hn, hj]

theorem selector_ne_marker (k : ℕ) (j : ℤ) (h : j ≠ -1) :
    selector k j ≠ PartitionMarked.marker := by
  simp only [selector, h, ↓reduceIte]
  split <;> decide

private theorem action_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (s next : Fin 4)
    (sm um om : Move) (x : Fin 5)
    (ht : program.transition s (fun i => (cfg f unary out p u q s).tape i
        ((cfg f unary out p u q s).head i)) =
      some (next, action (fun i => (cfg f unary out p u q s).tape i
        ((cfg f unary out p u q s).head i)) sm um om x)) :
    step program (cfg f unary out p u q s) =
      some (cfg f unary (Function.update out q x)
        (p + sm.offset) (u + um.offset) (q + om.offset) next) := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [action]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm] <;> intro hj <;> rw [hj]

private theorem advance_step (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hf : f p ≠ blank) (hu : unary u ≠ blank) :
    step program (cfg f unary out p u q 0) = some (cfg f unary out (p + 1) (u + 1) q 0) := by
  have ht := action_step f unary out p u q 0 0 .right .right .stay (out q)
    (by simp [program, cfg, hf, hu])
  simpa [Move.offset] using ht

private theorem choose_step (b : Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hf : f p = bitSymbol b) (hu : unary u = blank) :
    step program (cfg f unary out p u q 0) =
      some (cfg f unary out (p - 1) (u - 1) q (remember b)) := by
  have ht := action_step f unary out p u q 0 (remember b) .left .left .stay (out q)
    (by cases b <;> simp [program, cfg, hf, hu, bitSymbol, blank])
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem back_step (b : Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hu : unary u ≠ PartitionMarked.marker) :
    step program (cfg f unary out p u q (remember b)) =
      some (cfg f unary out (p - 1) (u - 1) q (remember b)) := by
  have ht := action_step f unary out p u q (remember b) (remember b) .left .left .stay (out q)
    (by cases b <;> simp [program, cfg, remember, hu])
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem flag_step (b : Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hu : unary u = PartitionMarked.marker) :
    step program (cfg f unary out p u q (remember b)) =
      some (cfg f unary (Function.update out q (bitSymbol b)) (p + 1) (u + 1) (q + 1) 3) := by
  have ht := action_step f unary out p u q (remember b) 3 .right .right .right (bitSymbol b)
    (by cases b <;> simp [program, cfg, remember, hu])
  simpa [Move.offset] using ht

private theorem copy_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p ≠ separator) :
    step program (cfg f unary out p u q 3) =
      some (cfg f unary (Function.update out q (f p)) (p + 1) u (q + 1) 3) := by
  have ht := action_step f unary out p u q 3 3 .right .stay .right (f p)
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem delimiter_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p = separator) :
    step program (cfg f unary out p u q 3) =
      some (cfg f unary (Function.update out q separator) (p + 1) u (q + 1) 0) := by
  have ht := action_step f unary out p u q 3 0 .right .stay .right separator
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem halt (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p = blank) :
    step program (cfg f unary out p u q 0) = none := by simp [step, program, cfg, h]

private theorem advance_run (prebits : List Bool) (f out : ℤ → Fin 5)
    (p q : ℤ) (k u : ℕ) (hu : u + prebits.length ≤ k) :
    run program prebits.length
      (cfg (putWord f p (prebits.map bitSymbol)) (selector k) out p u q 0) =
      some (cfg (putWord f p (prebits.map bitSymbol)) (selector k) out
        (p + prebits.length) (u + prebits.length) q 0) := by
  induction prebits generalizing f p u with
  | nil => simp [run]
  | cons b rest ih =>
    have hs := advance_step (putWord f p ((b :: rest).map bitSymbol)) (selector k) out p u q
      (by rw [List.map_cons, putWord_head]; cases b <;> decide)
      (by rw [selector_inside k u (by simp only [List.length_cons] at hu; omega)]; decide)
    simp only [List.length_cons, run, hs, Option.bind_some]
    have hr := ih (Function.update f p (bitSymbol b)) (p + 1) (u + 1) (by
      simp only [List.length_cons] at hu
      omega)
    simpa only [← putWord_cons, List.map_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

private theorem back_run (b : Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → unary (u - j) ≠ PartitionMarked.marker) :
    run program n (cfg f unary out p u q (remember b)) =
      some (cfg f unary out (p - n) (u - n) q (remember b)) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      back_step b f unary out (p - n) (u - n) q (h n (by omega))

private theorem putWord_cut (f : ℤ → Fin 5) (p : ℤ) (xs ys : List (Fin 5)) (x : Fin 5) :
    putWord f p (xs ++ x :: ys) (p + xs.length) = x := by
  rw [← putWord_append_forward, putWord_head]

/-- The unary-controlled selection round trip preserves both source tapes and
puts the selected bit on the output before any original payload is copied. -/
private theorem select_run (prebits suffix : List Bool) (b : Bool)
    (f out : ℤ → Fin 5) (p q : ℤ) :
    run program (2 * prebits.length + 2)
      (cfg (putWord f p (recordWord (prebits ++ b :: suffix))) (selector prebits.length) out p 0 q 0) =
      some (cfg (putWord f p (recordWord (prebits ++ b :: suffix))) (selector prebits.length)
        (Function.update out q (bitSymbol b)) p 0 (q + 1) 3) := by
  let k := prebits.length
  let src := putWord f p (recordWord (prebits ++ b :: suffix))
  have hword : recordWord (prebits ++ b :: suffix) =
      prebits.map bitSymbol ++ recordWord (b :: suffix) := by
    simp [recordWord, List.map_append, List.append_assoc]
  have ha := advance_run prebits (putWord f (p + k) (recordWord (b :: suffix))) out p q k 0
    (by dsimp [k]; omega)
  have hsource : putWord (putWord f (p + k) (recordWord (b :: suffix))) p
      (prebits.map bitSymbol) = src := by
    dsimp [src, k]
    rw [hword, putWord_append, List.length_map]
  rw [hsource] at ha
  simp only [Nat.cast_zero, zero_add] at ha
  have hselected : src (p + k) = bitSymbol b := by
    dsimp [src, k]
    rw [hword]
    simpa only [recordWord, List.map_cons, List.cons_append, List.length_map] using
      putWord_cut f p (prebits.map bitSymbol) (suffix.map bitSymbol ++ [separator]) (bitSymbol b)
  have hc := choose_step b src (selector k) out (p + k) k q hselected (selector_end k)
  have hb := back_run b src (selector k) out (p + k - 1) (k - 1 : ℤ) q k (by
    intro j hj
    apply selector_ne_marker
    dsimp [k] at *
    omega)
  have hsp : p + (k : ℤ) - 1 - k = p - 1 := by omega
  have hup : (k : ℤ) - 1 - k = -1 := by omega
  rw [hsp, hup] at hb
  have he := flag_step b src (selector k) out (p - 1) (-1) q (selector_left k)
  have hback : p - 1 + 1 = p := by omega
  rw [hback] at he
  have htime : 2 * prebits.length + 2 = ((k + 1) + k) + 1 := by dsimp [k]; omega
  rw [htime, run_add, run_add, run_add, ha]
  simp only [k] at hc hb he
  simp only [k, Option.bind_some, run_one, hc, hb, he]
  rfl

/-- Copy a complete record after its selected flag has been emitted. -/
private theorem copy_record (bits : List Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ) :
    run program (recordWord bits).length
      (cfg (putWord f p (recordWord bits)) unary out p u q 3) =
      some (cfg (putWord f p (recordWord bits)) unary (putWord out q (recordWord bits))
        (p + (recordWord bits).length) u (q + (recordWord bits).length) 0) := by
  induction bits generalizing f out p q with
  | nil =>
    simpa only [recordWord, List.map_nil, List.nil_append, List.length_singleton,
      run_one, putWord, Nat.cast_one] using delimiter_step (Function.update f p separator) unary out p u q (by simp)
  | cons b rest ih =>
    have hs := copy_step (putWord f p (recordWord (b :: rest))) unary out p u q
      (by change putWord f p (bitSymbol b :: recordWord rest) p ≠ separator
          rw [putWord_head]; cases b <;> decide)
    simp only [recordWord, List.map_cons, List.cons_append, putWord_head] at hs
    simp only [recordWord, List.map_cons, List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p (bitSymbol b)) (Function.update out q (bitSymbol b))
      (p + 1) (q + 1)
    simpa only [← putWord_cons, recordWord, List.map_cons, List.cons_append,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- One record preserves all its original bits, prepending the physically
selected bit. Selection and rewind cost exactly two times the index plus two. -/
theorem record_run (k : ℕ) (bits : List Bool) (h : k < bits.length)
    (f out : ℤ → Fin 5) (p q : ℤ) :
    run program ((recordWord bits).length + 2 * k + 2)
      (cfg (putWord f p (recordWord bits)) (selector k) out p 0 q 0) =
      some (cfg (putWord f p (recordWord bits)) (selector k)
        (putWord out q (bitSymbol (keyAt k bits) :: recordWord bits))
        (p + (recordWord bits).length) 0 (q + (recordWord bits).length + 1) 0) := by
  obtain ⟨prebits, b, suffix, hk, rfl⟩ := split_key k bits h
  subst k
  rw [keyAt_split]
  have hs := select_run prebits suffix b f out p q
  have hc := copy_record (prebits ++ b :: suffix) f (selector prebits.length)
    (Function.update out q (bitSymbol b)) p 0 (q + 1)
  rw [← putWord_cons] at hc
  have htime : (recordWord (prebits ++ b :: suffix)).length + 2 * prebits.length + 2 =
      (2 * prebits.length + 2) + (recordWord (prebits ++ b :: suffix)).length := by omega
  rw [htime, run_add, hs]
  simp only [Option.bind_some]
  simpa only [add_assoc, add_comm, add_left_comm] using hc

/-- A whole stream executes at its literal input volume plus the unary selection
and rewind cost for each record. Both original tapes are unchanged everywhere. -/
theorem stream_run (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) (f out : ℤ → Fin 5) (p q : ℤ) :
    run program ((encode records).length + records.length * (2 * k + 2))
      (cfg (putWord f p (encode records)) (selector k) out p 0 q 0) =
      some (cfg (putWord f p (encode records)) (selector k) (putWord out q (flagged k records))
        (p + (encode records).length) 0 (q + (flagged k records).length) 0) := by
  induction records generalizing f out p q with
  | nil => simp [encode, flagged, putWord, run]
  | cons bits rest ih =>
    let w := recordWord bits
    let fw := bitSymbol (keyAt k bits) :: w
    have hc := record_run k bits (hvalid bits (by simp))
      (putWord f (p + w.length) (encode rest)) out p q
    change run program (w.length + 2 * k + 2)
      (cfg (putWord (putWord f (p + w.length) (encode rest)) p w) (selector k) out p 0 q 0) =
      some (cfg (putWord (putWord f (p + w.length) (encode rest)) p w) (selector k)
        (putWord out q fw) (p + w.length) 0 (q + w.length + 1) 0) at hc
    rw [← putWord_append] at hc
    have hout : q + (w.length : ℤ) + 1 = q + fw.length := by
      simp only [fw, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega
    rw [hout] at hc
    have ht := ih (fun xs hxs => hvalid xs (by simp [hxs]))
      (putWord f p w) (putWord out q fw) (p + w.length) (q + fw.length)
    simp only [putWord_append_forward] at ht
    have htime : (encode (bits :: rest)).length + (bits :: rest).length * (2 * k + 2) =
        (w.length + 2 * k + 2) + ((encode rest).length + rest.length * (2 * k + 2)) := by
      simp only [encode, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      dsimp [w]
      omega
    rw [htime, run_add]
    change (run program (w.length + 2 * k + 2)
      (cfg (putWord f p (w ++ encode rest)) (selector k) out p 0 q 0)).bind _ = _
    rw [hc]
    simp only [Option.bind_some]
    simpa only [encode, flagged, List.length_append, Nat.cast_add, add_assoc] using ht

/-- Exact terminal execution, including the input terminator and arbitrary
untouched source/output background cells. -/
theorem stream_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) (f out : ℤ → Fin 5) (p q : ℤ)
    (hend : f (p + (encode records).length) = blank) :
    run program ((encode records).length + records.length * (2 * k + 2))
      (cfg (putWord f p (encode records)) (selector k) out p 0 q 0) =
      some (cfg (putWord f p (encode records)) (selector k) (putWord out q (flagged k records))
        (p + (encode records).length) 0 (q + (flagged k records).length) 0) ∧
    step program
      (cfg (putWord f p (encode records)) (selector k) (putWord out q (flagged k records))
        (p + (encode records).length) 0 (q + (flagged k records).length) 0) = none := by
  refine ⟨stream_run k records hvalid f out p q, halt _ _ _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr le_rfl), hend]

/-- A compositional whole-tape contract. The index is supplied as tape data;
`program` has three tapes and four states for every index and every record list. -/
theorem stream_hoare (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) (f out : ℤ → Fin 5) (p q : ℤ)
    (hend : f (p + (encode records).length) = blank) :
    HoareTime program
      (fun v => v = (cfg (putWord f p (encode records)) (selector k) out p 0 q 0).tapes)
      (fun v => v =
        (cfg (putWord f p (encode records)) (selector k) (putWord out q (flagged k records))
          (p + (encode records).length) 0 (q + (flagged k records).length) 0).tapes)
      ((encode records).length + records.length * (2 * k + 2)) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact k records hvalid f out p q hend
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

/-- With a blank output background, the result meets the global blank-tail
word convention, and the unary selector is restored for reuse. -/
theorem stream_to_blank (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    run program ((encode records).length + records.length * (2 * k + 2))
      (cfg (wordTape (encode records)) (selector k) (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (encode records)) (selector k) (wordTape (flagged k records))
        (encode records).length 0 (flagged k records).length 0) ∧
    step program (cfg (wordTape (encode records)) (selector k) (wordTape (flagged k records))
      (encode records).length 0 (flagged k records).length 0) = none := by
  have hw (xs : List (Fin 5)) : putWord (fun _ => blank) 0 xs = wordTape xs := by
    funext j
    simpa using putWord_blank 0 j xs
  simpa only [hw, zero_add] using
    stream_exact k records hvalid (fun _ => blank) (fun _ => blank) 0 0 rfl

end IntegerMultBounds.Machine.KeySelect
