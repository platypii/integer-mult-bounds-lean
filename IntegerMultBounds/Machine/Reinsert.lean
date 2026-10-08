import IntegerMultBounds.Machine.Partition

/-! Stable replacement of flagged records by a second record stream. Tape zero
holds the originals, tape one the replacements, and tape two the result. Each
false flag copies its original record; each true flag consumes exactly one
replacement. Both source tapes are preserved, and every visited source symbol
costs exactly one transition. -/

namespace IntegerMultBounds.Machine.Reinsert

open Partition (Record recordWord encode)

def source (replacement : Bool) : Fin 3 := if replacement then 1 else 0

def copying (replacement : Bool) : Fin 4 := if replacement then 3 else 1

def emit (replacement copy : Bool) (next : Fin 4) (symbols : Fin 3 → Fin 4) :
    Fin 4 × (Fin 3 → Fin 4 × Move) :=
  (next, fun i => if i = source replacement then (symbols i, .right)
    else if i = 2 ∧ copy then (symbols (source replacement), .right)
    else (symbols i, .stay))

/-- States: dispatch, copy original, skip original, copy replacement. -/
def program : Program 3 4 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then
      if symbols 0 = bitSymbol false then some (emit false true 1 symbols)
      else if symbols 0 = bitSymbol true then some (emit false false 2 symbols)
      else none
    else if s = 2 then
      some (emit false false (if symbols 0 = separator then 3 else 2) symbols)
    else
      let b := decide (s = 3)
      some (emit b true (if symbols (source b) = separator then 0 else copying b) symbols)

/-- The active source is `f`, the other source is `h`, and the destination is `g`. -/
def cfg (replacement : Bool) (f h g : ℤ → Fin 4) (p q r : ℤ) (s : Fin 4) :
    Config 3 4 0 where
  state := s
  head := fun i => if i = 2 then r else if i = source replacement then p else q
  tape := fun i => if i = 2 then g else if i = source replacement then f else h

theorem cfg_true (f h g : ℤ → Fin 4) (p q r : ℤ) (s : Fin 4) :
    cfg true f h g p q r s = cfg false h f g q p r s := by
  unfold cfg
  congr 1
  · funext i; fin_cases i <;> simp [source]
  · funext i; fin_cases i <;> simp [source]

private theorem emit_copy_step (b : Bool) (f h g : ℤ → Fin 4) (p q r : ℤ)
    (s next : Fin 4)
    (ht : program.transition s (fun i => (cfg b f h g p q r s).tape i
        ((cfg b f h g p q r s).head i)) =
      some (emit b true next (fun i => (cfg b f h g p q r s).tape i
        ((cfg b f h g p q r s).head i)))) :
    step program (cfg b f h g p q r s) =
      some (cfg b f h (Function.update g r (f p)) (p + 1) q (r + 1) next) := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [emit]
  congr 1
  congr 1
  · funext i; cases b <;> fin_cases i <;> simp [source, Move.offset]
  · funext i j
    cases b <;> fin_cases i <;> simp [source, Function.update_apply, eq_comm] <;>
      intro hj <;> rw [hj]

private theorem emit_skip_step (f h g : ℤ → Fin 4) (p q r : ℤ) (s next : Fin 4)
    (ht : program.transition s (fun i => (cfg false f h g p q r s).tape i
        ((cfg false f h g p q r s).head i)) =
      some (emit false false next (fun i => (cfg false f h g p q r s).tape i
        ((cfg false f h g p q r s).head i)))) :
    step program (cfg false f h g p q r s) =
      some (cfg false f h g (p + 1) q r next) := by
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [emit]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [source, Move.offset]
  · funext i j
    fin_cases i <;> simp [source, eq_comm] <;>
      intro hj <;> rw [hj]

theorem false_key_step (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hk : f p = bitSymbol false) :
    step program (cfg false f h g p q r 0) =
      some (cfg false f h (Function.update g r (bitSymbol false)) (p + 1) q (r + 1) 1) := by
  rw [← hk]
  apply emit_copy_step
  simp [program, cfg, source, hk]

theorem true_key_step (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hk : f p = bitSymbol true) :
    step program (cfg false f h g p q r 0) =
      some (cfg false f h g (p + 1) q r 2) := by
  apply emit_skip_step
  simp [program, cfg, source, hk, bitSymbol]

theorem copy_body_step (b : Bool) (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p ≠ separator) :
    step program (cfg b f h g p q r (copying b)) =
      some (cfg b f h (Function.update g r (f p)) (p + 1) q (r + 1) (copying b)) := by
  apply emit_copy_step
  cases b <;> simp [program, cfg, source, copying, hx]

theorem copy_delimiter_step (b : Bool) (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p = separator) :
    step program (cfg b f h g p q r (copying b)) =
      some (cfg b f h (Function.update g r separator) (p + 1) q (r + 1) 0) := by
  rw [← hx]
  apply emit_copy_step
  cases b <;> simp [program, cfg, source, copying, hx]

theorem skip_body_step (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p ≠ separator) :
    step program (cfg false f h g p q r 2) =
      some (cfg false f h g (p + 1) q r 2) := by
  apply emit_skip_step
  simp [program, cfg, source, hx]

theorem skip_delimiter_step (f h g : ℤ → Fin 4) (p q r : ℤ)
    (hx : f p = separator) :
    step program (cfg false f h g p q r 2) =
      some (cfg false f h g (p + 1) q r 3) := by
  apply emit_skip_step
  simp [program, cfg, source, hx]

theorem halt (f h g : ℤ → Fin 4) (p q r : ℤ) (hx : f p = blank) :
    step program (cfg false f h g p q r 0) = none := by
  simp [step, program, cfg, source, hx, blank, bitSymbol]

/-- Copy a delimiter-terminated word from either selected source. -/
theorem copy_body_run (b : Bool) (f h g : ℤ → Fin 4) (p q r : ℤ)
    (xs : List (Fin 4)) (hxs : ∀ x ∈ xs, x ≠ separator) :
    run program (xs.length + 1)
      (cfg b (putWord f p (xs ++ [separator])) h g p q r (copying b)) =
      some (cfg b (putWord f p (xs ++ [separator])) h
        (putWord g r (xs ++ [separator])) (p + (xs.length + 1)) q (r + (xs.length + 1)) 0) := by
  induction xs generalizing f g p r with
  | nil =>
    simpa only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add, run_one,
      putWord] using copy_delimiter_step b (Function.update f p separator) h g p q r (by simp)
  | cons x xs ih =>
    have hs := copy_body_step b (putWord f p ((x :: xs) ++ [separator])) h g p q r
      (by rw [List.cons_append, putWord_head]; exact hxs x (by simp))
    rw [List.cons_append, putWord_head] at hs
    simp only [List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p x) (Function.update g r x) (p + 1) (r + 1)
      (fun y hy => hxs y (by simp [hy]))
    simpa only [← putWord_cons, List.cons_append, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm, add_left_comm] using hr

/-- Skipping retains every source symbol and advances only the original head. -/
theorem skip_body_run (f h g : ℤ → Fin 4) (p q r : ℤ)
    (xs : List (Fin 4)) (hxs : ∀ x ∈ xs, x ≠ separator) :
    run program (xs.length + 1)
      (cfg false (putWord f p (xs ++ [separator])) h g p q r 2) =
      some (cfg false (putWord f p (xs ++ [separator])) h g (p + (xs.length + 1)) q r 3) := by
  induction xs generalizing f p with
  | nil =>
    simpa only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add, run_one,
      putWord] using skip_delimiter_step (Function.update f p separator) h g p q r (by simp)
  | cons x xs ih =>
    have hs := skip_body_step (putWord f p ((x :: xs) ++ [separator])) h g p q r
      (by rw [List.cons_append, putWord_head]; exact hxs x (by simp))
    rw [List.cons_append] at hs
    simp only [List.cons_append, List.length_cons]
    rw [run, hs]
    simp only [Option.bind_some]
    have hr := ih (Function.update f p x) (p + 1) (fun y hy => hxs y (by simp [hy]))
    simpa only [← putWord_cons, List.cons_append, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm, add_left_comm] using hr

private theorem bits_ne_separator (payload : List Bool) :
    ∀ x ∈ payload.map bitSymbol, x ≠ (separator : Fin 4) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  cases v <;> decide

/-- A retained original record costs exactly its encoded length. -/
theorem keep_record_run (payload : List Bool) (f h g : ℤ → Fin 4) (p q r : ℤ) :
    run program (recordWord false payload).length
      (cfg false (putWord f p (recordWord false payload)) h g p q r 0) =
      some (cfg false (putWord f p (recordWord false payload)) h
        (putWord g r (recordWord false payload))
        (p + (recordWord false payload).length) q (r + (recordWord false payload).length) 0) := by
  have hs := false_key_step (putWord f p (recordWord false payload)) h g p q r
    (putWord_head f p _ _)
  simp only [recordWord] at hs
  simp only [recordWord, List.length_cons]
  rw [run, hs]
  simp only [Option.bind_some]
  have hr := copy_body_run false (Function.update f p (bitSymbol false)) h
    (Function.update g r (bitSymbol false)) (p + 1) q (r + 1)
    (payload.map bitSymbol) (bits_ne_separator payload)
  simpa only [← putWord_cons, List.length_append, List.length_singleton,
    Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, copying, Bool.false_eq_true, ↓reduceIte] using hr

/-- A flagged original is skipped before replacement copying starts. -/
theorem skip_record_run (payload : List Bool) (f h g : ℤ → Fin 4) (p q r : ℤ) :
    run program (recordWord true payload).length
      (cfg false (putWord f p (recordWord true payload)) h g p q r 0) =
      some (cfg false (putWord f p (recordWord true payload)) h g
        (p + (recordWord true payload).length) q r 3) := by
  have hs := true_key_step (putWord f p (recordWord true payload)) h g p q r
    (putWord_head f p _ _)
  simp only [recordWord] at hs
  simp only [recordWord, List.length_cons]
  rw [run, hs]
  simp only [Option.bind_some]
  have hr := skip_body_run (Function.update f p (bitSymbol true)) h g (p + 1) q r
    (payload.map bitSymbol) (bits_ne_separator payload)
  simpa only [← putWord_cons, List.length_append, List.length_singleton,
    Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hr

/-- Every replacement key and payload is copied, regardless of its own key bit. -/
theorem replacement_record_run (rec : Record) (f h g : ℤ → Fin 4) (p q r : ℤ) :
    run program (recordWord rec.key rec.payload).length
      (cfg false f (putWord h q (recordWord rec.key rec.payload)) g p q r 3) =
      some (cfg false f (putWord h q (recordWord rec.key rec.payload))
        (putWord g r (recordWord rec.key rec.payload)) p
        (q + (recordWord rec.key rec.payload).length)
        (r + (recordWord rec.key rec.payload).length) 0) := by
  have hr := copy_body_run true h f g q p r
    (bitSymbol rec.key :: rec.payload.map bitSymbol) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | ht
      · cases rec.key <;> decide
      · exact bits_ne_separator rec.payload x ht)
  simpa only [List.cons_append, cfg_true, recordWord, List.length_cons,
    List.length_append, List.length_singleton, List.length_nil, copying, ↓reduceIte,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] using hr

/-- The number of replacements required by the flagged original stream. -/
def holes (records : List Record) : ℕ := (records.filter (fun rec => rec.key)).length

@[simp] theorem holes_nil : holes [] = 0 := rfl

@[simp] theorem holes_cons (b : Bool) (payload : List Bool) (rest : List Record) :
    holes (⟨b, payload⟩ :: rest) = holes rest + if b then 1 else 0 := by
  cases b <;> simp [holes, Nat.add_comm]

/-- Fill the flagged positions from left to right. When replacements are
insufficient the remaining flagged originals are retained; the tape theorem
below requires exact supply and never uses this fallback. -/
def fill : List Record → List Record → List Record
  | [], _ => []
  | rec :: rest, replacements =>
      if rec.key then
        match replacements with
        | [] => rec :: fill rest []
        | replacement :: tail => replacement :: fill rest tail
      else rec :: fill rest replacements

@[simp] theorem fill_nil (replacements : List Record) : fill [] replacements = [] := rfl

@[simp] theorem fill_false (payload : List Bool) (rest replacements : List Record) :
    fill (⟨false, payload⟩ :: rest) replacements =
      ⟨false, payload⟩ :: fill rest replacements := rfl

@[simp] theorem fill_true (payload : List Bool) (rest : List Record)
    (replacement : Record) (tail : List Record) :
    fill (⟨true, payload⟩ :: rest) (replacement :: tail) = replacement :: fill rest tail := rfl

/-- Stable hole filling preserves the number of record slots. -/
@[simp] theorem fill_length (records replacements : List Record) :
    (fill records replacements).length = records.length := by
  induction records generalizing replacements with
  | nil => rfl
  | cons rec rest ih =>
    rcases rec with ⟨b, payload⟩
    cases b <;> cases replacements <;> simp [fill, ih]

/-- Applying a repair to the selected records and reinserting that stream is
exactly pointwise repair at the flagged slots, even if repairs change key bits. -/
theorem fill_repair (repair : Record → Record) (records : List Record) :
    fill records ((records.filter (fun rec => rec.key)).map repair) =
      records.map (fun rec => if rec.key then repair rec else rec) := by
  induction records with
  | nil => rfl
  | cons rec rest ih =>
    rcases rec with ⟨b, payload⟩
    cases b <;> simp [fill, ih]

/-- Reinserting the unmodified selected stream restores the original exactly. -/
theorem fill_selected (records : List Record) :
    fill records (records.filter (fun rec => rec.key)) = records := by
  simpa using fill_repair id records

/-- The output contains every retained original and every supplied replacement
exactly once, so encoded volume is additive without equal-width assumptions. -/
theorem fill_volume (records replacements : List Record)
    (hc : replacements.length = holes records) :
    (encode (fill records replacements)).length =
      (Partition.bucket false records).length + (encode replacements).length := by
  induction records generalizing replacements with
  | nil =>
    have he : replacements = [] := List.length_eq_zero_iff.mp hc
    subst replacements
    rfl
  | cons rec rest ih =>
    rcases rec with ⟨b, payload⟩
    cases b with
    | false =>
      have hr := ih replacements (by simpa using hc)
      simpa only [fill_false, encode, Partition.bucket_cons, ↓reduceIte,
        List.length_append, Nat.add_assoc] using congrArg
          ((recordWord false payload).length + ·) hr
    | true =>
      cases replacements with
      | nil => simp at hc
      | cons replacement tail =>
        have hr := ih tail (by simpa using hc)
        simp only [fill_true, encode, Partition.bucket_cons, Bool.true_eq_false,
          ↓reduceIte, List.length_append]
        omega

/-- Exact complete-stream execution. The input tapes remain identical everywhere;
only the encoded result segment on the destination is overwritten. -/
theorem stream_run (records replacements : List Record)
    (f h g : ℤ → Fin 4) (p q r : ℤ) (hc : replacements.length = holes records) :
    run program ((encode records).length + (encode replacements).length)
      (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        g p q r 0) =
      some (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        (putWord g r (encode (fill records replacements)))
        (p + (encode records).length) (q + (encode replacements).length)
        (r + (encode (fill records replacements)).length) 0) := by
  induction records generalizing replacements f h g p q r with
  | nil =>
    have he : replacements = [] := List.length_eq_zero_iff.mp hc
    subst replacements
    simp [encode, putWord, run]
  | cons rec rest ih =>
    rcases rec with ⟨b, payload⟩
    cases b with
    | false =>
      have hc' : replacements.length = holes rest := by simpa using hc
      let w := recordWord false payload
      have hf := keep_record_run payload (putWord f (p + w.length) (encode rest))
        (putWord h q (encode replacements)) g p q r
      change run program w.length
        (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w)
          (putWord h q (encode replacements)) g p q r 0) =
        some (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w)
          (putWord h q (encode replacements)) (putWord g r w)
          (p + w.length) q (r + w.length) 0) at hf
      rw [← putWord_append] at hf
      have ht := ih replacements (putWord f p w) h (putWord g r w)
        (p + w.length) q (r + w.length) hc'
      simp only [putWord_append_forward] at ht
      simp only [encode, List.length_append, Nat.add_assoc, run_add]
      rw [hf]
      simp only [Option.bind_some]
      simpa only [fill_false, encode, List.length_append, Nat.cast_add, add_assoc,
        run_add] using ht
    | true =>
      cases replacements with
      | nil => simp at hc
      | cons replacement tail =>
        have hc' : tail.length = holes rest := by simpa using hc
        let w := recordWord true payload
        let v := recordWord replacement.key replacement.payload
        have hs := skip_record_run payload (putWord f (p + w.length) (encode rest))
          (putWord h q (v ++ encode tail)) g p q r
        change run program w.length
          (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w)
            (putWord h q (v ++ encode tail)) g p q r 0) =
          some (cfg false (putWord (putWord f (p + w.length) (encode rest)) p w)
            (putWord h q (v ++ encode tail)) g (p + w.length) q r 3) at hs
        rw [← putWord_append] at hs
        have hr := replacement_record_run replacement (putWord f p (w ++ encode rest))
          (putWord h (q + v.length) (encode tail)) g (p + w.length) q r
        change run program v.length
          (cfg false (putWord f p (w ++ encode rest))
            (putWord (putWord h (q + v.length) (encode tail)) q v) g (p + w.length) q r 3) =
          some (cfg false (putWord f p (w ++ encode rest))
            (putWord (putWord h (q + v.length) (encode tail)) q v)
            (putWord g r v) (p + w.length) (q + v.length) (r + v.length) 0) at hr
        rw [← putWord_append] at hr
        have ht := ih tail (putWord f p w) (putWord h q v) (putWord g r v)
          (p + w.length) (q + v.length) (r + v.length) hc'
        simp only [putWord_append_forward] at ht
        have htime : (encode (⟨true, payload⟩ :: rest)).length +
            (encode (replacement :: tail)).length =
            w.length + (v.length + ((encode rest).length + (encode tail).length)) := by
          simp only [encode, List.length_append, w, v]
          omega
        rw [htime]
        simp only [encode]
        rw [run_add, hs]
        simp only [Option.bind_some]
        rw [run_add, hr]
        simp only [Option.bind_some]
        simpa only [fill_true, encode, List.length_append, Nat.cast_add, add_assoc] using ht

/-- With a blank after the originals, the finite machine halts at the exact
claimed time, having consumed the entire supplied replacement stream. -/
theorem stream_exact (records replacements : List Record)
    (f h g : ℤ → Fin 4) (p q r : ℤ) (hc : replacements.length = holes records)
    (hend : f (p + (encode records).length) = blank) :
    run program ((encode records).length + (encode replacements).length)
      (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        g p q r 0) =
      some (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        (putWord g r (encode (fill records replacements)))
        (p + (encode records).length) (q + (encode replacements).length)
        (r + (encode (fill records replacements)).length) 0) ∧
    step program (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        (putWord g r (encode (fill records replacements)))
        (p + (encode records).length) (q + (encode replacements).length)
        (r + (encode (fill records replacements)).length) 0) = none := by
  refine ⟨stream_run records replacements f h g p q r hc, halt _ _ _ _ _ _ ?_⟩
  rw [putWord_outside _ _ _ _ (Or.inr le_rfl), hend]

/-- Blank-backed streams yield the complete output tape, blank outside the exact
encoded result, while both input tapes are retained everywhere. -/
theorem stream_blank (records replacements : List Record)
    (hc : replacements.length = holes records) :
    run program ((encode records).length + (encode replacements).length)
      (cfg false (wordTape (encode records)) (wordTape (encode replacements))
        (fun _ => blank) 0 0 0 0) =
      some (cfg false (wordTape (encode records)) (wordTape (encode replacements))
        (wordTape (encode (fill records replacements)))
        (encode records).length (encode replacements).length
        (encode (fill records replacements)).length 0) ∧
    step program (cfg false (wordTape (encode records)) (wordTape (encode replacements))
        (wordTape (encode (fill records replacements)))
        (encode records).length (encode replacements).length
        (encode (fill records replacements)).length 0) = none := by
  have hw (xs : List (Fin 4)) : putWord (fun _ => blank) 0 xs = wordTape xs := by
    funext j
    simpa using putWord_blank 0 j xs
  simpa only [hw, zero_add] using stream_exact records replacements
    (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 hc rfl

/-- A full-tape Hoare contract with the actual transition count. -/
theorem stream_hoare (records replacements : List Record)
    (f h g : ℤ → Fin 4) (p q r : ℤ) (hc : replacements.length = holes records)
    (hend : f (p + (encode records).length) = blank) :
    HoareTime program
      (fun v => v = (cfg false (putWord f p (encode records))
        (putWord h q (encode replacements)) g p q r 0).tapes)
      (fun v => v = (cfg false (putWord f p (encode records)) (putWord h q (encode replacements))
        (putWord g r (encode (fill records replacements)))
        (p + (encode records).length) (q + (encode replacements).length)
        (r + (encode (fill records replacements)).length) 0).tapes)
      ((encode records).length + (encode replacements).length) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := stream_exact records replacements f h g p q r hc hend
  exact ⟨(encode records).length + (encode replacements).length, _, le_rfl, hr, hh, rfl⟩

end IntegerMultBounds.Machine.Reinsert
