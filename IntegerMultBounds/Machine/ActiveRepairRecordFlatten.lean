import IntegerMultBounds.Machine.DropFlag

/-! Literal two-state removal of record flags and delimiters. Payload bits
are copied contiguously, source retention/erasure is explicit, and every
source symbol costs one transition independently of record widths. -/

namespace IntegerMultBounds.Machine.ActiveRepairRecordFlatten

def retained (erase : Bool) (x : Fin 5) : Fin 5 := if erase then blank else x

/-- State zero skips a flag; state one copies bits and skips the delimiter. -/
def program (erase : Bool) : Program 2 2 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 0 = blank then none else
        some (1, fun i => if i = 0 then (retained erase (symbols 0), .right)
          else (symbols i, .stay))
    else some (if symbols 0 = separator then 0 else 1,
      fun i => if i = 0 then (retained erase (symbols 0),.right)
        else if symbols 0 = separator then (symbols i,.stay) else (symbols 0,.right))

def cfg (f out : ℤ → Fin 5) (p q : ℤ) (s : Fin 2) : Config 2 2 1 where
  state := s
  head := fun i => if i = 0 then p else q
  tape := fun i => if i = 0 then f else out

private theorem skip_step (erase : Bool) (f out : ℤ → Fin 5) (p q : ℤ)
    (h : f p ≠ blank) :
    step (program erase) (cfg f out p q 0) =
      some (cfg (Function.update f p (retained erase (f p))) out (p + 1) q 1) := by
  simp only [step, program, cfg, ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i <;> simp [Function.update_apply, eq_comm]
    intro hj
    rw [hj]

private theorem copy_step (erase : Bool) (f out : ℤ → Fin 5) (p q : ℤ)
    (h : f p ≠ separator) :
    step (program erase) (cfg f out p q 1) =
      some (cfg (Function.update f p (retained erase (f p)))
        (Function.update out q (f p)) (p + 1) (q + 1) 1) := by
  simp only [step, program, cfg, show (1 : Fin 2) ≠ 0 by decide,
    ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j; fin_cases i <;> simp [Function.update_apply, eq_comm]

private theorem delimiter_step (erase : Bool) (f out : ℤ → Fin 5) (p q : ℤ)
    (h : f p = separator) :
    step (program erase) (cfg f out p q 1) =
      some (cfg (Function.update f p (retained erase separator))
        out (p + 1) q 0) := by
  simp only [step, program, cfg, show (1 : Fin 2) ≠ 0 by decide,
    ↓reduceIte, h, Move.offset]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp
  · funext i j
    fin_cases i
    · simp [Function.update_apply,eq_comm]
    · simp [eq_comm]
      intro hj
      rw [hj]

private theorem halt (erase : Bool) (f out : ℤ → Fin 5) (p q : ℤ)
    (h : f p = blank) : step (program erase) (cfg f out p q 0) = none := by
  simp [step, program, cfg, h]

def payloadWord (bits : List Bool) : List (Fin 5) := bits.map bitSymbol

def raw : List Partition.Record → List (Fin 5)
  | [] => []
  | r::rs => payloadWord r.payload ++ raw rs

private theorem payload_run (erase : Bool) (bits : List Bool)
    (f out : ℤ → Fin 5) (p q : ℤ) :
    run (program erase) (KeySelect.recordWord bits).length
      (cfg (putWord f p (KeySelect.recordWord bits)) out p q 1) =
      some (cfg (putWord f p ((KeySelect.recordWord bits).map (retained erase)))
        (putWord out q (payloadWord bits))
        (p + (KeySelect.recordWord bits).length) (q + (payloadWord bits).length) 0) := by
  induction bits generalizing f out p q with
  | nil =>
    simpa only [KeySelect.recordWord,List.map_nil,List.nil_append,List.map_cons,
      List.length_singleton,run_one,putWord,Nat.cast_one,Function.update_idem,
      payloadWord,List.length_nil,Nat.cast_zero,add_zero] using
      delimiter_step erase (Function.update f p separator) out p q (by simp)
  | cons b rest ih =>
    have hs := copy_step erase (putWord f p (KeySelect.recordWord (b::rest))) out p q
      (by change putWord f p (bitSymbol b :: KeySelect.recordWord rest) p ≠ separator
          rw [putWord_head]; cases b <;> decide)
    simp only [KeySelect.recordWord,List.map_cons,List.cons_append,putWord_head] at hs
    rw [putWord_replace_head] at hs
    simp only [KeySelect.recordWord,List.map_cons,List.cons_append,List.length_cons]
    rw [run,hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p (retained erase (bitSymbol b)))
      (Function.update out q (bitSymbol b)) (p+1) (q+1)
    simpa only [←putWord_cons,KeySelect.recordWord,List.map_cons,List.cons_append,
      payloadWord,List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm,payloadWord] using hr

def recordWord (rec : Partition.Record) : List (Fin 5) :=
  bitSymbol rec.key :: KeySelect.recordWord rec.payload

def encode : List Partition.Record → List (Fin 5)
  | [] => []
  | rec :: rest => recordWord rec ++ encode rest

/-- This input format is exactly the five-symbol widening of Partition's format. -/
theorem encode_partition (records : List Partition.Record) :
    encode records = (Partition.encode records).map PartitionMarked.encoding.encode := by
  induction records with
  | nil => rfl
  | cons rec rest ih =>
    simp only [encode, Partition.encode, Partition.recordWord, List.map_append,
      List.map_cons, List.map_map, ih, recordWord, KeySelect.recordWord]
    rfl

/-- No ordering hypothesis: flags can be removed after any stable sorting pass. -/
theorem record_run (erase : Bool) (rec : Partition.Record)
    (f out : ℤ → Fin 5) (p q : ℤ) :
    run (program erase) (recordWord rec).length
      (cfg (putWord f p (recordWord rec)) out p q 0) =
      some (cfg (putWord f p ((recordWord rec).map (retained erase)))
        (putWord out q (payloadWord rec.payload))
        (p + (recordWord rec).length) (q + (payloadWord rec.payload).length) 0) := by
  have hs := skip_step erase (putWord f p (recordWord rec)) out p q
    (by rw [recordWord, putWord_head]; cases rec.key <;> decide)
  simp only [recordWord, putWord_head] at hs
  rw [putWord_replace_head] at hs
  simp only [recordWord, List.length_cons, run, hs, Option.bind_some]
  have hr := payload_run erase rec.payload (Function.update f p (retained erase (bitSymbol rec.key)))
    out (p + 1) q
  simpa only [List.map_cons, ← putWord_cons, List.length_cons, Nat.cast_add,
    Nat.cast_one, add_assoc, add_comm, add_left_comm,payloadWord] using hr

/-- Exact one-transition-per-input-symbol execution with whole-tape source and
output descriptions, even when source erasure is enabled. -/
theorem stream_run (erase : Bool) (records : List Partition.Record)
    (f out : ℤ → Fin 5) (p q : ℤ) :
    run (program erase) (encode records).length
      (cfg (putWord f p (encode records)) out p q 0) =
      some (cfg (putWord f p ((encode records).map (retained erase)))
        (putWord out q (raw records))
        (p + (encode records).length)
        (q + (raw records).length) 0) := by
  induction records generalizing f out p q with
  | nil => simp [encode, raw, putWord, run]
  | cons rec rest ih =>
    let w := recordWord rec
    let payload := payloadWord rec.payload
    have hc := record_run erase rec (putWord f (p + w.length) (encode rest)) out p q
    change run (program erase) w.length
      (cfg (putWord (putWord f (p + w.length) (encode rest)) p w) out p q 0) =
      some (cfg (putWord (putWord f (p + w.length) (encode rest)) p (w.map (retained erase)))
        (putWord out q payload) (p + w.length) (q + payload.length) 0) at hc
    rw [← putWord_append] at hc
    have hs : putWord (putWord f (p + w.length) (encode rest)) p (w.map (retained erase)) =
        putWord (putWord f p (w.map (retained erase))) (p + w.length) (encode rest) := by
      have hleft := putWord_append f p (w.map (retained erase)) (encode rest)
      have hright := putWord_append_forward f p (w.map (retained erase)) (encode rest)
      simp only [List.length_map] at hleft hright
      exact hleft.symm.trans hright.symm
    rw [hs] at hc
    have ht := ih (putWord f p (w.map (retained erase))) (putWord out q payload)
      (p + w.length) (q + payload.length)
    have htape : putWord (putWord f p (w.map (retained erase))) (p + w.length)
        ((encode rest).map (retained erase)) =
        putWord f p ((w ++ encode rest).map (retained erase)) := by
      rw [List.map_append]
      simpa only [List.length_map] using
        putWord_append_forward f p (w.map (retained erase)) ((encode rest).map (retained erase))
    rw [htape, putWord_append_forward] at ht
    simp only [encode, List.length_append, run_add]
    rw [hc]
    simp only [Option.bind_some]
    simpa only [List.map_cons, raw, List.length_append, Nat.cast_add, add_assoc] using ht

/-- The next source cell is unchanged by erasure and gives an actual halt. -/
theorem stream_exact (erase : Bool) (records : List Partition.Record)
    (f out : ℤ → Fin 5) (p q : ℤ) (hend : f (p + (encode records).length) = blank) :
    run (program erase) (encode records).length
      (cfg (putWord f p (encode records)) out p q 0) =
      some (cfg (putWord f p ((encode records).map (retained erase)))
        (putWord out q (raw records))
        (p + (encode records).length)
        (q + (raw records).length) 0) ∧
    step (program erase)
      (cfg (putWord f p ((encode records).map (retained erase)))
        (putWord out q (raw records))
        (p + (encode records).length)
        (q + (raw records).length) 0) = none := by
  refine ⟨stream_run erase records f out p q, halt erase _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr (by simp)), hend]

theorem stream_hoare (erase : Bool) (records : List Partition.Record)
    (f out : ℤ → Fin 5) (p q : ℤ) (hend : f (p + (encode records).length) = blank) :
    HoareTime (program erase)
      (fun v => v = (cfg (putWord f p (encode records)) out p q 0).tapes)
      (fun v => v = (cfg (putWord f p ((encode records).map (retained erase)))
        (putWord out q (raw records))
        (p + (encode records).length)
        (q + (raw records).length) 0).tapes)
      (encode records).length := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact erase records f out p q hend
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩


end IntegerMultBounds.Machine.ActiveRepairRecordFlatten
