import IntegerMultBounds.Machine.DropFlag
import IntegerMultBounds.Machine.PartitionMarked
import IntegerMultBounds.Machine.ReturnOrigin

/-! Flag one record and extract it when its key says so. The key tape holds a
flag bit followed by the destination bits over a marked blank tape. The
four-tape, six-state control rewrites the record's flag on the output stream,
and, for a flagged record, first moves the destination bits to the extracted
stream and then copies the record behind them in the raw keyed format. The key
tape is erased back to its marked blank state with its head at the origin; the
source is retained literally. -/

namespace IntegerMultBounds.Machine.FlagCopy

open PartitionMarked (marker markedTape)

private def act (symbols : Fin 4 → Fin 5) (kw ow ew : Fin 5) (sm km om em : Move) :
    Fin 4 → Fin 5 × Move :=
  fun i => (if i = 0 then symbols 0 else if i = 1 then kw else if i = 2 then ow else ew,
    if i = 0 then sm else if i = 1 then km else if i = 2 then om else em)

/-- States: zero reads the flag, one copies an unflagged record to the output,
two moves the destination bits to the extracted stream, three rewinds the key
tape, four copies a flagged record to both streams, five halts. -/
def program : Program 4 6 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 1 = bitSymbol false then
        some (1, act symbols blank (symbols 1) (symbols 3) .right .stay .right .stay)
      else if symbols 1 = bitSymbol true then
        some (2, act symbols blank (symbols 1) (symbols 3) .right .right .right .stay)
      else none
    else if s = 1 then
      some (if symbols 0 = separator then 5 else 1,
        act symbols (symbols 1) (symbols 0) (symbols 3) .right .stay .right .stay)
    else if s = 2 then
      if symbols 1 = blank then
        some (3, act symbols blank (symbols 2) (bitSymbol true) .stay .left .stay .right)
      else some (2, act symbols blank (symbols 2) (symbols 1) .stay .right .stay .right)
    else if s = 3 then
      if symbols 1 = marker then
        some (4, act symbols (symbols 1) (symbols 2) (symbols 3) .stay .right .stay .stay)
      else some (3, act symbols (symbols 1) (symbols 2) (symbols 3) .stay .left .stay .stay)
    else if s = 4 then
      some (if symbols 0 = separator then 5 else 4,
        act symbols (symbols 1) (symbols 0) (symbols 0) .right .stay .right .right)
    else none

def cfg (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (s : Fin 6) : Config 4 6 1 where
  state := s
  head := fun i => if i = 0 then p else if i = 1 then u else if i = 2 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else if i = 2 then out else ext

/-- The key tape: a word at the origin over a marked blank tape. -/
def keyTape (w : List (Fin 5)) : ℤ → Fin 5 := putWord (markedTape 0 []) 0 w

private theorem act_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (s next : Fin 6)
    (kw ow ew : Fin 5) (sm km om em : Move)
    (ht : program.transition s (fun i => (cfg f g out ext p u q r s).tape i
        ((cfg f g out ext p u q r s).head i)) =
      some (next, act (fun i => (cfg f g out ext p u q r s).tape i
        ((cfg f g out ext p u q r s).head i)) kw ow ew sm km om em)) :
    step program (cfg f g out ext p u q r s) =
      some (cfg f (Function.update g u kw) (Function.update out q ow) (Function.update ext r ew)
        (p + sm.offset) (u + km.offset) (q + om.offset) (r + em.offset) next) := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [act]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    all_goals (intro hj; rw [hj])

theorem halt (f g out ext : ℤ → Fin 5) (p u q r : ℤ) :
    step program (cfg f g out ext p u q r 5) = none := by
  simp [step, program, cfg]

private theorem flag_false_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ)
    (h : g u = bitSymbol false) :
    step program (cfg f g out ext p u q r 0) =
      some (cfg f (Function.update g u blank) (Function.update out q (bitSymbol false)) ext
        (p + 1) u (q + 1) r 1) := by
  have ht := act_step f g out ext p u q r 0 1 blank (g u) (ext r) .right .stay .right .stay
    (by simp [program, cfg, h])
  simpa [Move.offset, h] using ht

private theorem flag_true_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ)
    (h : g u = bitSymbol true) :
    step program (cfg f g out ext p u q r 0) =
      some (cfg f (Function.update g u blank) (Function.update out q (bitSymbol true)) ext
        (p + 1) (u + 1) (q + 1) r 2) := by
  have ht := act_step f g out ext p u q r 0 2 blank (g u) (ext r) .right .right .right .stay
    (by simp [program, cfg, h, show (bitSymbol true : Fin 5) ≠ bitSymbol false by decide])
  simpa [Move.offset, h] using ht

private theorem copy_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : f p ≠ separator) :
    step program (cfg f g out ext p u q r 1) =
      some (cfg f g (Function.update out q (f p)) ext (p + 1) u (q + 1) r 1) := by
  have ht := act_step f g out ext p u q r 1 1 (g u) (f p) (ext r) .right .stay .right .stay
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem delimiter_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : f p = separator) :
    step program (cfg f g out ext p u q r 1) =
      some (cfg f g (Function.update out q separator) ext (p + 1) u (q + 1) r 5) := by
  have ht := act_step f g out ext p u q r 1 5 (g u) (f p) (ext r) .right .stay .right .stay
    (by simp [program, cfg, h])
  simpa [Move.offset, h] using ht

private theorem move_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : g u ≠ blank) :
    step program (cfg f g out ext p u q r 2) =
      some (cfg f (Function.update g u blank) out (Function.update ext r (g u))
        p (u + 1) q (r + 1) 2) := by
  have ht := act_step f g out ext p u q r 2 2 blank (out q) (g u) .stay .right .stay .right
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem move_end_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : g u = blank) :
    step program (cfg f g out ext p u q r 2) =
      some (cfg f g out (Function.update ext r (bitSymbol true)) p (u - 1) q (r + 1) 3) := by
  have ht := act_step f g out ext p u q r 2 3 blank (out q) (bitSymbol true) .stay .left .stay .right
    (by simp [program, cfg, h])
  rw [← h] at ht
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem rewind_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : g u ≠ marker) :
    step program (cfg f g out ext p u q r 3) =
      some (cfg f g out ext p (u - 1) q r 3) := by
  have ht := act_step f g out ext p u q r 3 3 (g u) (out q) (ext r) .stay .left .stay .stay
    (by simp [program, cfg, h])
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem marker_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : g u = marker) :
    step program (cfg f g out ext p u q r 3) =
      some (cfg f g out ext p (u + 1) q r 4) := by
  have ht := act_step f g out ext p u q r 3 4 (g u) (out q) (ext r) .stay .right .stay .stay
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem both_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : f p ≠ separator) :
    step program (cfg f g out ext p u q r 4) =
      some (cfg f g (Function.update out q (f p)) (Function.update ext r (f p))
        (p + 1) u (q + 1) (r + 1) 4) := by
  have ht := act_step f g out ext p u q r 4 4 (g u) (f p) (f p) .right .stay .right .right
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem both_end_step (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (h : f p = separator) :
    step program (cfg f g out ext p u q r 4) =
      some (cfg f g (Function.update out q separator) (Function.update ext r separator)
        (p + 1) u (q + 1) (r + 1) 5) := by
  have ht := act_step f g out ext p u q r 4 5 (g u) (f p) (f p) .right .stay .right .right
    (by simp [program, cfg, h])
  simpa [Move.offset, h] using ht

/-! ### Runs over whole segments -/

/-- Copy a raw record word to the output stream from the unflagged state. -/
private theorem copy_run (payload : List Bool) (f g out ext : ℤ → Fin 5) (p u q r : ℤ) :
    run program (KeySelect.recordWord payload).length
      (cfg (putWord f p (KeySelect.recordWord payload)) g out ext p u q r 1) =
      some (cfg (putWord f p (KeySelect.recordWord payload)) g
        (putWord out q (KeySelect.recordWord payload)) ext
        (p + (KeySelect.recordWord payload).length) u
        (q + (KeySelect.recordWord payload).length) r 5) := by
  induction payload generalizing f out p q with
  | nil =>
    simpa only [KeySelect.recordWord, List.map_nil, List.nil_append, List.length_singleton,
      run_one, putWord, Nat.cast_one] using
      delimiter_step (Function.update f p separator) g out ext p u q r (by simp)
  | cons b rest ih =>
    have hs := copy_step (putWord f p (KeySelect.recordWord (b :: rest))) g out ext p u q r
      (by change putWord f p (bitSymbol b :: KeySelect.recordWord rest) p ≠ separator
          rw [putWord_head]; cases b <;> decide)
    simp only [KeySelect.recordWord, List.map_cons, List.cons_append, putWord_head] at hs
    simp only [KeySelect.recordWord, List.map_cons, List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p (bitSymbol b)) (Function.update out q (bitSymbol b))
      (p + 1) (q + 1)
    simpa only [← putWord_cons, KeySelect.recordWord, List.map_cons, List.cons_append,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Copy a raw record word to both streams from the flagged state. -/
private theorem both_run (payload : List Bool) (f g out ext : ℤ → Fin 5) (p u q r : ℤ) :
    run program (KeySelect.recordWord payload).length
      (cfg (putWord f p (KeySelect.recordWord payload)) g out ext p u q r 4) =
      some (cfg (putWord f p (KeySelect.recordWord payload)) g
        (putWord out q (KeySelect.recordWord payload))
        (putWord ext r (KeySelect.recordWord payload))
        (p + (KeySelect.recordWord payload).length) u
        (q + (KeySelect.recordWord payload).length)
        (r + (KeySelect.recordWord payload).length) 5) := by
  induction payload generalizing f out ext p q r with
  | nil =>
    simpa only [KeySelect.recordWord, List.map_nil, List.nil_append, List.length_singleton,
      run_one, putWord, Nat.cast_one] using
      both_end_step (Function.update f p separator) g out ext p u q r (by simp)
  | cons b rest ih =>
    have hs := both_step (putWord f p (KeySelect.recordWord (b :: rest))) g out ext p u q r
      (by change putWord f p (bitSymbol b :: KeySelect.recordWord rest) p ≠ separator
          rw [putWord_head]; cases b <;> decide)
    simp only [KeySelect.recordWord, List.map_cons, List.cons_append, putWord_head] at hs
    simp only [KeySelect.recordWord, List.map_cons, List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p (bitSymbol b)) (Function.update out q (bitSymbol b))
      (Function.update ext r (bitSymbol b)) (p + 1) (q + 1) (r + 1)
    simpa only [← putWord_cons, KeySelect.recordWord, List.map_cons, List.cons_append,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Move the destination bits from the key tape to the extracted stream, erasing
them, then write the flag bit of the extracted record on the blank terminator. -/
private theorem move_run (bits : List Bool) (f g out ext : ℤ → Fin 5) (p u q r : ℤ)
    (hend : g (u + bits.length) = blank) :
    run program (bits.length + 1)
      (cfg f (putWord g u (bits.map bitSymbol)) out ext p u q r 2) =
      some (cfg f (putWord g u (List.replicate bits.length blank)) out
        (putWord ext r (bits.map bitSymbol ++ [bitSymbol true]))
        p (u + bits.length - 1) q (r + bits.length + 1) 3) := by
  induction bits generalizing g ext u r with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    simp only [List.length_nil, List.map_nil, List.replicate_zero, putWord, zero_add, run_one,
      Nat.cast_zero, add_zero, List.nil_append]
    rw [move_end_step f g out ext p u q r hend]
  | cons b rest ih =>
    have hs := move_step f (putWord g u ((b :: rest).map bitSymbol)) out ext p u q r
      (by rw [List.map_cons, putWord_head]; cases b <;> decide)
    simp only [List.map_cons, putWord_head] at hs
    simp only [List.length_cons, List.map_cons, List.replicate_succ, List.cons_append]
    rw [show rest.length + 1 + 1 = 1 + (rest.length + 1) by omega, run_add, run_one, hs]
    simp only [Option.bind_some]
    rw [putWord_replace_head, putWord_cons (x := blank), putWord_cons (x := bitSymbol b)]
    have hr := ih (Function.update g u blank) (Function.update ext r (bitSymbol b)) (u + 1) (r + 1)
      (by rw [Function.update_of_ne (by omega)]; convert hend using 2
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

private theorem rewind_run (f g out ext : ℤ → Fin 5) (p u q r : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → g (u - j) ≠ marker) :
    run program n (cfg f g out ext p u q r 3) = some (cfg f g out ext p (u - n) q r 3) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      rewind_step f g out ext p (u - n) q r (h n (by omega))

/-! ### Key tape bookkeeping -/

theorem keyTape_nil (j : ℤ) (hj : 0 ≤ j) : keyTape [] j = blank := by
  simp only [keyTape, putWord, markedTape, show j ≠ (0 : ℤ) - 1 by omega, ↓reduceIte]
  rfl

theorem keyTape_marker : keyTape [] (-1) = marker := by
  simp [keyTape, putWord, markedTape]

/-- Erasing the whole key word restores the marked blank tape. -/
private theorem erased_eq (n : ℕ) :
    putWord (Function.update (keyTape []) 0 blank) 1 (List.replicate n blank) = keyTape [] := by
  funext j
  by_cases hj : 1 ≤ j ∧ j < 1 + n
  · have hmem := ReturnOrigin.putWord_mem (Function.update (keyTape []) 0 blank) 1
      (List.replicate n blank) j (by simpa using hj)
    rw [List.mem_replicate] at hmem
    rw [hmem.2, keyTape_nil j (by omega)]
  · rw [putWord_outside _ _ _ _ (by simp only [List.length_replicate]; omega)]
    by_cases h0 : j = 0
    · subst j; simp [keyTape_nil]
    · rw [Function.update_of_ne h0]

/-! ### One record -/

/-- An unflagged record: skip its stored flag, write the flag from the key tape,
copy the payload. The key tape returns to its marked blank state. -/
theorem record_false (b : Bool) (payload : List Bool) (f out ext : ℤ → Fin 5) (p q r : ℤ) :
    run program (payload.length + 2)
      (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩)) (keyTape [bitSymbol false])
        out ext p 0 q r 0) =
      some (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩)) (keyTape [])
        (putWord out q (DropFlag.recordWord ⟨false, payload⟩)) ext
        (p + (payload.length + 2)) 0 (q + (payload.length + 2)) r 5) := by
  have hs := flag_false_step (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
    (keyTape [bitSymbol false]) out ext p 0 q r (by simp [keyTape, putWord])
  have hkey : Function.update (keyTape [bitSymbol false]) 0 blank = keyTape [] := by
    simpa [keyTape, putWord] using erased_eq 0
  rw [hkey] at hs
  have hc := copy_run payload (Function.update f p (bitSymbol b)) (keyTape [])
    (Function.update out q (bitSymbol false)) ext (p + 1) 0 (q + 1) r
  have hlen : (KeySelect.recordWord payload).length = payload.length + 1 := by
    simp [KeySelect.recordWord]
  rw [hlen] at hc
  rw [show payload.length + 2 = 1 + (payload.length + 1) by omega, run_add, run_one]
  simp only [DropFlag.recordWord, putWord_cons] at hs hc ⊢
  rw [hs]
  simp only [Option.bind_some]
  rw [hc]
  congr 2 <;> push_cast <;> ring

/-- A flagged record: write its flag, move the destination bits to the
extracted stream, rewind the key tape, then copy the record behind the bits.
The cost is the record length plus twice the key width plus three. -/
theorem record_true (b : Bool) (payload bits : List Bool) (f out ext : ℤ → Fin 5) (p q r : ℤ) :
    run program (payload.length + 2 + (2 * bits.length + 3))
      (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
        (keyTape (bitSymbol true :: bits.map bitSymbol)) out ext p 0 q r 0) =
      some (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩)) (keyTape [])
        (putWord out q (DropFlag.recordWord ⟨true, payload⟩))
        (putWord ext r (KeySelect.recordWord (bits ++ true :: payload)))
        (p + (payload.length + 2)) 0 (q + (payload.length + 2))
        (r + (bits.length + (payload.length + 2))) 5) := by
  -- the flag step
  have hs := flag_true_step (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
    (keyTape (bitSymbol true :: bits.map bitSymbol)) out ext p 0 q r (by simp [keyTape, putWord])
  have hkey : Function.update (keyTape (bitSymbol true :: bits.map bitSymbol)) 0 blank =
      putWord (Function.update (keyTape []) 0 blank) 1 (bits.map bitSymbol) := by
    simp only [keyTape, putWord_replace_head, zero_add]
    rfl
  rw [hkey] at hs
  simp only [zero_add] at hs
  -- moving the bits
  have hm := move_run bits (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
    (Function.update (keyTape []) 0 blank) (Function.update out q (bitSymbol true)) ext
    (p + 1) 1 (q + 1) r (by
      rw [Function.update_of_ne (by omega), keyTape_nil _ (by omega)])
  -- rewinding the key tape
  have hw := rewind_run (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
    (putWord (Function.update (keyTape []) 0 blank) 1 (List.replicate bits.length blank))
    (Function.update out q (bitSymbol true))
    (putWord ext r (bits.map bitSymbol ++ [bitSymbol true])) (p + 1) (1 + bits.length - 1) (q + 1)
    (r + bits.length + 1) (bits.length + 1) (by
      intro j hj
      rw [erased_eq]
      apply PartitionMarked.markedTape_ne_marker
      omega)
  have hmk := marker_step (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
    (putWord (Function.update (keyTape []) 0 blank) 1 (List.replicate bits.length blank))
    (Function.update out q (bitSymbol true))
    (putWord ext r (bits.map bitSymbol ++ [bitSymbol true])) (p + 1)
    (1 + bits.length - 1 - (bits.length + 1 : ℕ)) (q + 1) (r + bits.length + 1) (by
      rw [erased_eq, show (1 : ℤ) + bits.length - 1 - (bits.length + 1 : ℕ) = -1 by push_cast; ring]
      exact keyTape_marker)
  rw [erased_eq] at hw hmk
  -- copying the record
  have hc := both_run payload (Function.update f p (bitSymbol b)) (keyTape [])
    (Function.update out q (bitSymbol true)) (putWord ext r (bits.map bitSymbol ++ [bitSymbol true]))
    (p + 1) (1 + bits.length - 1 - (bits.length + 1 : ℕ) + 1) (q + 1) (r + bits.length + 1)
  have hlen : (KeySelect.recordWord payload).length = payload.length + 1 := by
    simp [KeySelect.recordWord]
  rw [hlen, ← putWord_cons, ← putWord_cons] at hc
  have hext : putWord (putWord ext r (bits.map bitSymbol ++ [bitSymbol true])) (r + bits.length + 1)
      (KeySelect.recordWord payload) =
      putWord ext r (KeySelect.recordWord (bits ++ true :: payload)) := by
    have := putWord_append_forward ext r (bits.map bitSymbol ++ [bitSymbol true])
      (KeySelect.recordWord payload)
    simp only [List.length_append, List.length_map, List.length_singleton, Nat.cast_add,
      Nat.cast_one, ← add_assoc] at this
    rw [this]
    congr 1
    simp [KeySelect.recordWord, List.map_append, List.map_cons]
  rw [hext] at hc
  -- assemble
  rw [show payload.length + 2 + (2 * bits.length + 3) =
    1 + (bits.length + 1) + (bits.length + 1) + 1 + (payload.length + 1) by omega,
    run_add, run_add, run_add, run_add, run_one]
  simp only [DropFlag.recordWord] at hs hm hw hmk hc ⊢
  rw [hs]
  simp only [Option.bind_some]
  rw [hm]
  simp only [Option.bind_some]
  rw [erased_eq, hw]
  simp only [Option.bind_some, run_one]
  rw [hmk]
  simp only [Option.bind_some]
  rw [hc]
  congr 2 <;> push_cast <;> ring

/-! ### The contract for one record of either kind -/

/-- The key word supplied by the key routine: the flag, then the destination
bits when the record is flagged. -/
def keyWord (flag : Bool) (bits : List Bool) : List (Fin 5) :=
  bitSymbol flag :: if flag then bits.map bitSymbol else []

/-- The raw keyed record appended to the extracted stream. -/
def extractedWord (flag : Bool) (bits payload : List Bool) : List (Fin 5) :=
  if flag then KeySelect.recordWord (bits ++ true :: payload) else []

def cost (flag : Bool) (bits payload : List Bool) : ℕ :=
  payload.length + 2 + if flag then 2 * bits.length + 3 else 0

theorem extractedWord_length (flag : Bool) (bits payload : List Bool) :
    (extractedWord flag bits payload).length =
      if flag then bits.length + (payload.length + 2) else 0 := by
  cases flag <;> simp [extractedWord, KeySelect.recordWord]

theorem record_hoare (flag b : Bool) (payload bits : List Bool) (f out ext : ℤ → Fin 5)
    (p q r : ℤ) :
    HoareTime program
      (fun v => v = (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩))
        (keyTape (keyWord flag bits)) out ext p 0 q r 0).tapes)
      (fun v => v = (cfg (putWord f p (DropFlag.recordWord ⟨b, payload⟩)) (keyTape [])
        (putWord out q (DropFlag.recordWord ⟨flag, payload⟩))
        (putWord ext r (extractedWord flag bits payload))
        (p + (payload.length + 2)) 0 (q + (payload.length + 2))
        (r + (extractedWord flag bits payload).length) 5).tapes)
      (cost flag bits payload) := by
  rintro v rfl
  cases flag
  · have hr := record_false b payload f out ext p q r
    refine ⟨_, _, le_rfl, ?_, halt _ _ _ _ _ _ _ _, rfl⟩
    change run program (cost false bits payload) (cfg _ (keyTape (keyWord false bits)) _ _ _ _ _ _ 0) = _
    simpa [keyWord, extractedWord, cost, putWord] using hr
  · have hr := record_true b payload bits f out ext p q r
    refine ⟨_, _, le_rfl, ?_, halt _ _ _ _ _ _ _ _, rfl⟩
    change run program (cost true bits payload) (cfg _ (keyTape (keyWord true bits)) _ _ _ _ _ _ 0) = _
    simp only [keyWord, extractedWord, cost, KeySelect.recordWord, ↓reduceIte, List.map_append,
      List.map_cons, List.length_append, List.length_map, List.length_cons,
      List.append_assoc, List.cons_append, Nat.cast_add, Nat.cast_one]
    convert hr using 3
    · simp [KeySelect.recordWord, List.map_append, List.map_cons]
    · simp only [List.length_nil, Nat.cast_zero, zero_add]; ring

end IntegerMultBounds.Machine.FlagCopy
