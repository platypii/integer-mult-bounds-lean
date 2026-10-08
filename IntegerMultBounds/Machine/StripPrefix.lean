import IntegerMultBounds.Machine.KeySelect

/-! Remove a unary-counted key pre from every delimiter-terminated raw
record. The three-tape, four-state control first rewinds the unary width tape
from wherever a previous pass left its head, then, per record, advances the
source over the pre in lockstep with the width tape, rewinds the width tape
to its origin, and copies the remainder through the delimiter. The source and
width tapes are retained literally; every rewind is an actual left transition. -/

namespace IntegerMultBounds.Machine.StripPrefix

open KeySelect (selector recordWord encode)

private def action (symbols : Fin 3 → Fin 5) (sm um om : Move) (out : Fin 5) :
    Fin 3 → Fin 5 × Move :=
  fun i => (if i = 2 then out else symbols i,
    if i = 0 then sm else if i = 1 then um else om)

/-- States: zero rewinds the width tape initially, one scans the pre, two
rewinds the width tape before copying, three copies the remainder. -/
def program : Program 3 4 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 1 then
      if symbols 0 = blank then none
      else if symbols 1 = blank then some (2, action symbols .stay .left .stay (symbols 2))
      else some (1, action symbols .right .right .stay (symbols 2))
    else if s = 3 then
      some ((if symbols 0 = separator then 1 else 3), action symbols .right .stay .right (symbols 0))
    else if symbols 1 = PartitionMarked.marker then
      some ((if s = 0 then 1 else 3), action symbols .stay .right .stay (symbols 2))
    else some (s, action symbols .stay .left .stay (symbols 2))

def cfg (f unary out : ℤ → Fin 5) (p u q : ℤ) (s : Fin 4) : Config 3 4 1 where
  state := s
  head := fun i => if i = 0 then p else if i = 1 then u else q
  tape := fun i => if i = 0 then f else if i = 1 then unary else out

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

/-- Rewinding states keep every head but the width head. -/
def rewinding (s : Fin 4) : Prop := s = 0 ∨ s = 2

private theorem rewind_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (s : Fin 4)
    (hs : rewinding s) (hu : unary u ≠ PartitionMarked.marker) :
    step program (cfg f unary out p u q s) = some (cfg f unary out p (u - 1) q s) := by
  have ht := action_step f unary out p u q s s .stay .left .stay (out q)
    (by rcases hs with rfl | rfl <;> simp [program, cfg, hu])
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem marker_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (s : Fin 4)
    (hs : rewinding s) (hu : unary u = PartitionMarked.marker) :
    step program (cfg f unary out p u q s) =
      some (cfg f unary out p (u + 1) q (if s = 0 then 1 else 3)) := by
  have ht := action_step f unary out p u q s (if s = 0 then 1 else 3) .stay .right .stay (out q)
    (by rcases hs with rfl | rfl <;> simp [program, cfg, hu])
  simpa [Move.offset] using ht

private theorem advance_step (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hf : f p ≠ blank) (hu : unary u ≠ blank) :
    step program (cfg f unary out p u q 1) = some (cfg f unary out (p + 1) (u + 1) q 1) := by
  have ht := action_step f unary out p u q 1 1 .right .right .stay (out q)
    (by simp [program, cfg, hf, hu])
  simpa [Move.offset] using ht

private theorem enter_step (f unary out : ℤ → Fin 5) (p u q : ℤ)
    (hf : f p ≠ blank) (hu : unary u = blank) :
    step program (cfg f unary out p u q 1) = some (cfg f unary out p (u - 1) q 2) := by
  have ht := action_step f unary out p u q 1 2 .stay .left .stay (out q)
    (by simp [program, cfg, hf, hu])
  simpa [Move.offset, sub_eq_add_neg] using ht

private theorem copy_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p ≠ separator) :
    step program (cfg f unary out p u q 3) =
      some (cfg f unary (Function.update out q (f p)) (p + 1) u (q + 1) 3) := by
  have ht := action_step f unary out p u q 3 3 .right .stay .right (f p)
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem delimiter_step (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p = separator) :
    step program (cfg f unary out p u q 3) =
      some (cfg f unary (Function.update out q separator) (p + 1) u (q + 1) 1) := by
  have ht := action_step f unary out p u q 3 1 .right .stay .right separator
    (by simp [program, cfg, h])
  simpa [Move.offset] using ht

private theorem halt (f unary out : ℤ → Fin 5) (p u q : ℤ) (h : f p = blank) :
    step program (cfg f unary out p u q 1) = none := by simp [step, program, cfg, h]

private theorem rewind_run (f unary out : ℤ → Fin 5) (p u q : ℤ) (s : Fin 4)
    (hs : rewinding s) (n : ℕ)
    (h : ∀ j : ℕ, j < n → unary (u - j) ≠ PartitionMarked.marker) :
    run program n (cfg f unary out p u q s) = some (cfg f unary out p (u - n) q s) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      rewind_step f unary out p (u - n) q s hs (h n (by omega))

/-- From any nonnegative width-head position, the rewinding state reaches the
marker and steps back to the origin. -/
private theorem rewind_origin (f out : ℤ → Fin 5) (p q : ℤ) (k h : ℕ) (s : Fin 4)
    (hs : rewinding s) :
    run program (h + 2) (cfg f (selector k) out p h q s) =
      some (cfg f (selector k) out p 0 q (if s = 0 then 1 else 3)) := by
  have hr := rewind_run f (selector k) out p h q s hs (h + 1) (by
    intro j hj
    apply KeySelect.selector_ne_marker
    omega)
  have hm := marker_step f (selector k) out p (-1) q s hs (KeySelect.selector_left k)
  have hh : (h : ℤ) - ((h + 1 : ℕ) : ℤ) = -1 := by push_cast; ring
  rw [hh] at hr
  rw [show h + 2 = (h + 1) + 1 by omega, run_add, hr]
  simp only [Option.bind_some, run_one, hm]
  rfl

private theorem advance_run (prebits : List Bool) (f out : ℤ → Fin 5)
    (p q : ℤ) (k u : ℕ) (hu : u + prebits.length ≤ k) :
    run program prebits.length
      (cfg (putWord f p (prebits.map bitSymbol)) (selector k) out p u q 1) =
      some (cfg (putWord f p (prebits.map bitSymbol)) (selector k) out
        (p + prebits.length) (u + prebits.length) q 1) := by
  induction prebits generalizing f p u with
  | nil => simp [run]
  | cons b rest ih =>
    have hs := advance_step (putWord f p ((b :: rest).map bitSymbol)) (selector k) out p u q
      (by rw [List.map_cons, putWord_head]; cases b <;> decide)
      (by rw [KeySelect.selector_inside k u (by simp only [List.length_cons] at hu; omega)]; decide)
    simp only [List.length_cons, run, hs, Option.bind_some]
    have hr := ih (Function.update f p (bitSymbol b)) (p + 1) (u + 1) (by
      simp only [List.length_cons] at hu
      omega)
    simpa only [← putWord_cons, List.map_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Copy the remainder of a record after its pre was skipped. -/
private theorem copy_record (bits : List Bool) (f unary out : ℤ → Fin 5) (p u q : ℤ) :
    run program (recordWord bits).length
      (cfg (putWord f p (recordWord bits)) unary out p u q 3) =
      some (cfg (putWord f p (recordWord bits)) unary (putWord out q (recordWord bits))
        (p + (recordWord bits).length) u (q + (recordWord bits).length) 1) := by
  induction bits generalizing f out p q with
  | nil =>
    simpa only [recordWord, List.map_nil, List.nil_append, List.length_singleton,
      run_one, putWord, Nat.cast_one] using
      delimiter_step (Function.update f p separator) unary out p u q (by simp)
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

/-- After entering from the end of the width tape, the rewinding state returns
the width head to the origin and starts copying, for every width. -/
private theorem rewind_pred (f out : ℤ → Fin 5) (p q : ℤ) (k : ℕ) :
    run program (k + 1) (cfg f (selector k) out p ((k : ℤ) - 1) q 2) =
      some (cfg f (selector k) out p 0 q 3) := by
  cases k with
  | zero =>
    simp only [Nat.cast_zero, zero_sub, zero_add, run_one]
    rw [marker_step f (selector 0) out p (-1) q 2 (Or.inr rfl) (KeySelect.selector_left 0)]
    rfl
  | succ k =>
    have hr := rewind_origin f out p q (k + 1) k 2 (Or.inr rfl)
    rw [show k + 1 + 1 = k + 2 from rfl]
    simpa using hr

/-- One record: skip its pre of the unary width, rewind, and copy the rest.
The cost is the remainder word plus twice the width plus two. -/
theorem record_run (pre rest : List Bool) (f out : ℤ → Fin 5) (p q : ℤ) :
    run program ((recordWord rest).length + 2 * pre.length + 2)
      (cfg (putWord f p (recordWord (pre ++ rest))) (selector pre.length) out p 0 q 1) =
      some (cfg (putWord f p (recordWord (pre ++ rest))) (selector pre.length)
        (putWord out q (recordWord rest))
        (p + (recordWord (pre ++ rest)).length) 0 (q + (recordWord rest).length) 1) := by
  have hword : recordWord (pre ++ rest) = pre.map bitSymbol ++ recordWord rest := by
    simp [recordWord, List.map_append, List.append_assoc]
  have hsource : putWord (putWord f (p + pre.length) (recordWord rest)) p
      (pre.map bitSymbol) = putWord f p (recordWord (pre ++ rest)) := by
    rw [hword, putWord_append, List.length_map]
  have hsrc2 : putWord (putWord f p (pre.map bitSymbol)) (p + pre.length) (recordWord rest) =
      putWord f p (recordWord (pre ++ rest)) := by
    have := putWord_append_forward f p (pre.map bitSymbol) (recordWord rest)
    rw [List.length_map] at this
    rw [this, hword]
  have ha := advance_run pre (putWord f (p + pre.length) (recordWord rest)) out p q
    pre.length 0 (by omega)
  rw [hsource] at ha
  simp only [Nat.cast_zero, zero_add] at ha
  have hne : putWord f p (recordWord (pre ++ rest)) (p + pre.length) ≠ blank := by
    rw [← hsrc2]
    cases rest with
    | nil => rw [show recordWord [] = [separator] from rfl, putWord_head]; decide
    | cons b r =>
      rw [show recordWord (b :: r) = bitSymbol b :: recordWord r from rfl, putWord_head]
      cases b <;> decide
  have he := enter_step (putWord f p (recordWord (pre ++ rest))) (selector pre.length) out
    (p + pre.length) pre.length q hne (KeySelect.selector_end pre.length)
  have hb := rewind_pred (putWord f p (recordWord (pre ++ rest))) out (p + pre.length) q
    pre.length
  have hc := copy_record rest (putWord f p (pre.map bitSymbol)) (selector pre.length) out
    (p + pre.length) 0 q
  rw [hsrc2] at hc
  have hlen : (p + (pre.length : ℤ)) + ((recordWord rest).length : ℤ) =
      p + ((recordWord (pre ++ rest)).length : ℤ) := by
    rw [hword, List.length_append, List.length_map]
    push_cast
    ring
  rw [hlen] at hc
  have htime : (recordWord rest).length + 2 * pre.length + 2 =
      (pre.length + 1) + ((pre.length + 1) + (recordWord rest).length) := by omega
  rw [htime, run_add, run_add, ha]
  simp only [Option.bind_some, run_one, he]
  rw [run_add, hb]
  simp only [Option.bind_some]
  exact hc

/-- The stripped stream: each record loses its first `k` bits. -/
def stripped (k : ℕ) (records : List (List Bool)) : List (List Bool) := records.map (List.drop k)

theorem stripped_length (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k ≤ bits.length) :
    (encode (stripped k records)).length + records.length * k = (encode records).length := by
  induction records with
  | nil => simp [stripped, encode]
  | cons bits rest ih =>
    have hb := hvalid bits (by simp)
    have ih' := ih (fun xs hxs => hvalid xs (by simp [hxs]))
    simp only [stripped, List.map_cons, encode, recordWord, List.length_append, List.length_map,
      List.length_drop, List.length_cons, Nat.add_mul, Nat.one_mul] at ih' ⊢
    omega

/-- A whole stream from the scanning state: its literal volume plus the width
plus two per record. Source and width tapes are unchanged everywhere. -/
theorem stream_run (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k ≤ bits.length) (f out : ℤ → Fin 5) (p q : ℤ) :
    run program ((encode records).length + records.length * (k + 2))
      (cfg (putWord f p (encode records)) (selector k) out p 0 q 1) =
      some (cfg (putWord f p (encode records)) (selector k)
        (putWord out q (encode (stripped k records)))
        (p + (encode records).length) 0 (q + (encode (stripped k records)).length) 1) := by
  induction records generalizing f out p q with
  | nil => simp [encode, stripped, putWord, run]
  | cons bits rest ih =>
    have hb := hvalid bits (by simp)
    have hsplit : bits.take k ++ bits.drop k = bits := List.take_append_drop k bits
    have hk : (bits.take k).length = k := by rw [List.length_take]; omega
    let w := recordWord bits
    let dw := recordWord (bits.drop k)
    have hc := record_run (bits.take k) (bits.drop k)
      (putWord f (p + w.length) (encode rest)) out p q
    rw [hk, hsplit] at hc
    change run program (dw.length + 2 * k + 2)
      (cfg (putWord (putWord f (p + w.length) (encode rest)) p w) (selector k) out p 0 q 1) =
      some (cfg (putWord (putWord f (p + w.length) (encode rest)) p w) (selector k)
        (putWord out q dw) (p + w.length) 0 (q + dw.length) 1) at hc
    rw [← putWord_append] at hc
    have ht := ih (fun xs hxs => hvalid xs (by simp [hxs]))
      (putWord f p w) (putWord out q dw) (p + w.length) (q + dw.length)
    simp only [putWord_append_forward] at ht
    have hw : w.length = k + dw.length := by
      simp only [w, dw, recordWord, List.length_append, List.length_map, List.length_singleton,
        List.length_drop]
      omega
    have htime : (encode (bits :: rest)).length + (bits :: rest).length * (k + 2) =
        (dw.length + 2 * k + 2) + ((encode rest).length + rest.length * (k + 2)) := by
      simp only [encode, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      dsimp only [w, dw] at hw ⊢
      omega
    rw [htime, run_add]
    change (run program (dw.length + 2 * k + 2)
      (cfg (putWord f p (w ++ encode rest)) (selector k) out p 0 q 1)).bind _ = _
    rw [hc]
    simp only [Option.bind_some]
    simpa only [encode, stripped, List.map_cons, List.length_append, Nat.cast_add, add_assoc] using ht

/-- Exact terminal execution from the scanning state, including the halt on
the input terminator. -/
theorem stream_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k ≤ bits.length) (f out : ℤ → Fin 5) (p q : ℤ)
    (hend : f (p + (encode records).length) = blank) :
    run program ((encode records).length + records.length * (k + 2))
      (cfg (putWord f p (encode records)) (selector k) out p 0 q 1) =
      some (cfg (putWord f p (encode records)) (selector k)
        (putWord out q (encode (stripped k records)))
        (p + (encode records).length) 0 (q + (encode (stripped k records)).length) 1) ∧
    step program (cfg (putWord f p (encode records)) (selector k)
        (putWord out q (encode (stripped k records)))
        (p + (encode records).length) 0 (q + (encode (stripped k records)).length) 1) = none := by
  refine ⟨stream_run k records hvalid f out p q, halt _ _ _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr le_rfl), hend]

/-- The complete program: from any nonnegative width-head position, rewind,
then strip every record. The width tape is restored with its head at the
origin, the source is retained literally, and the output is the stripped
stream in the raw record format. -/
theorem strip_hoare (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k ≤ bits.length) (f out : ℤ → Fin 5) (p q : ℤ) (h : ℕ)
    (hend : f (p + (encode records).length) = blank) :
    HoareTime program
      (fun v => v = (cfg (putWord f p (encode records)) (selector k) out p h q 0).tapes)
      (fun v => v = (cfg (putWord f p (encode records)) (selector k)
        (putWord out q (encode (stripped k records)))
        (p + (encode records).length) 0 (q + (encode (stripped k records)).length) 1).tapes)
      (h + 2 + ((encode records).length + records.length * (k + 2))) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact k records hvalid f out p q hend
  refine ⟨_, _, le_rfl, ?_, hh, rfl⟩
  change run program _ (cfg (putWord f p (encode records)) (selector k) out p h q 0) = _
  rw [run_add, rewind_origin _ _ _ _ k h 0 (Or.inl rfl)]
  simp only [Option.bind_some, ↓reduceIte]
  exact hr

end IntegerMultBounds.Machine.StripPrefix
