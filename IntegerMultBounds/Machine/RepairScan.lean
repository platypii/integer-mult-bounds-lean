import IntegerMultBounds.Machine.FlagCopy
import IntegerMultBounds.Machine.MarkedReturn
import IntegerMultBounds.Machine.LoopChain
import IntegerMultBounds.Machine.RepairStage
import IntegerMultBounds.Machine.CounterTape
import IntegerMultBounds.Machine.GrowingCounter
import Mathlib.Data.List.GetD

/-! The flagging and extraction scan of the exceptional-address repair (§5),
on the same fourteen-slot bank as the sort, strip and reinsert stage. A
binary rank counter drives the scan. Each iteration first runs a key routine
`K`, which reads the rank and writes the flag and destination bits of the
current record on the key tape, then copies the record with its new flag to
the flagged full stream, extracting a flagged record in the raw keyed format,
and finally increments the counter. The key routine is a parameter with a
per-record contract; the manuscript's arithmetic (membership in `ℬ`, reversal
of the eight modular additions, destination rank) is its content. -/

namespace IntegerMultBounds.Machine.RepairScan

open PartitionMarked (marker markedTape encoding)
open RepairStage (Keyed rawOf raw encTape stage hoare_extend_eq hoare_place hoare_widen)
open Partition (Record)

/-! ### Flagging and extraction at the list level -/

/-- The input records with their flags rewritten from position `j` on. -/
def flagged (flag : ℕ → Bool) : ℕ → List Record → List Record
  | _, [] => []
  | j, r :: rs => ⟨flag j, r.payload⟩ :: flagged flag (j + 1) rs

/-- The flagged records with their key bits, from position `j` on. -/
def items (flag : ℕ → Bool) (bits : ℕ → List Bool) : ℕ → List Record → List Keyed
  | _, [] => []
  | j, r :: rs =>
    (if flag j then [(bits j, ⟨true, r.payload⟩)] else []) ++ items flag bits (j + 1) rs

variable (flag : ℕ → Bool) (bits : ℕ → List Bool)

theorem flagged_append (j : ℕ) (l₁ l₂ : List Record) :
    flagged flag j (l₁ ++ l₂) = flagged flag j l₁ ++ flagged flag (j + l₁.length) l₂ := by
  induction l₁ generalizing j with
  | nil => simp [flagged]
  | cons r rs ih => simp [flagged, ih, Nat.add_assoc, Nat.add_comm 1]

theorem items_append (j : ℕ) (l₁ l₂ : List Record) :
    items flag bits j (l₁ ++ l₂) = items flag bits j l₁ ++ items flag bits (j + l₁.length) l₂ := by
  induction l₁ generalizing j with
  | nil => simp [items]
  | cons r rs ih => simp [items, ih, Nat.add_assoc, Nat.add_comm 1]

theorem flagged_length (j : ℕ) (rs : List Record) : (flagged flag j rs).length = rs.length := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih => simp [flagged, ih]

theorem items_length (j : ℕ) (rs : List Record) :
    (items flag bits j rs).length = Reinsert.holes (flagged flag j rs) := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    simp only [items, flagged, List.length_append, ih, Reinsert.holes, List.filter_cons]
    cases flag j <;> simp [Nat.add_comm]

theorem items_keys (k j : ℕ) (rs : List Record) (hk : ∀ i, j ≤ i → i < j + rs.length → (bits i).length = k) :
    ∀ x ∈ items flag bits j rs, x.1.length = k := by
  induction rs generalizing j with
  | nil => simp [items]
  | cons r rs ih =>
    intro x hx
    simp only [items, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact hk j le_rfl (by simp)
      · simp at hx
    · exact ih (j + 1) (fun i hi hi' => hk i (by omega) (by simp only [List.length_cons]; omega)) x hx

theorem dropFlag_encode_append (l₁ l₂ : List Record) :
    DropFlag.encode (l₁ ++ l₂) = DropFlag.encode l₁ ++ DropFlag.encode l₂ := by
  induction l₁ with
  | nil => rfl
  | cons r rs ih => simp [DropFlag.encode, ih]

theorem keySelect_encode_append (l₁ l₂ : List (List Bool)) :
    KeySelect.encode (l₁ ++ l₂) = KeySelect.encode l₁ ++ KeySelect.encode l₂ := by
  induction l₁ with
  | nil => rfl
  | cons r rs ih => simp [KeySelect.encode, ih]

/-- The raw extracted word of one record is the flag copier's output. -/
theorem raw_items_single (j : ℕ) (r : Record) :
    KeySelect.encode (raw (items flag bits j [r])) =
      FlagCopy.extractedWord (flag j) (bits j) r.payload := by
  simp only [items, List.append_nil, FlagCopy.extractedWord]
  cases flag j <;> simp [raw, rawOf, KeySelect.encode]

/-! ### The rank counter -/

/-- The counter tape in the widened alphabet: the separator at the origin and
the bits from position one. -/
def ctrTape (bs : List Bool) : ℤ → Fin 5 :=
  fun j => encoding.encode (putBits GrowingCounter.emptyTape 1 bs j)

/-- The counter after `j` increments from `c` zero bits. -/
def counter (c j : ℕ) : List Bool := Counter.advance j (List.replicate c false)

theorem advance_succ' (n : ℕ) (bs : List Bool) :
    Counter.advance (n + 1) bs = Counter.increment (Counter.advance n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => rw [Counter.advance, ih, Counter.advance]

theorem advance_length (n : ℕ) (bs : List Bool) : (Counter.advance n bs).length = bs.length := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => rw [Counter.advance, ih, Counter.increment_length]

theorem counter_length (c j : ℕ) : (counter c j).length = c := by
  simp [counter, advance_length]

theorem counter_succ (c j : ℕ) : counter c (j + 1) = Counter.increment (counter c j) :=
  advance_succ' j _

/-- The telescoped carry cost of `n` increments from zero. -/
theorem carry_sum (c n : ℕ) :
    ∑ j ∈ Finset.range n, 2 * CounterTape.carrySteps (counter c j) +
      2 * Counter.weight (counter c n) ≤ 6 * n + 2 * Counter.weight (counter c 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, counter_succ]
    have := CounterTape.increment_potential (counter c n)
    omega

theorem weight_zero (c : ℕ) : Counter.weight (counter c 0) = 0 := by
  simp only [counter, Counter.advance]
  induction c with
  | zero => rfl
  | succ c ih => simpa [List.replicate_succ, Counter.weight] using ih

theorem carry_sum_le (c n : ℕ) :
    ∑ j ∈ Finset.range n, 2 * CounterTape.carrySteps (counter c j) ≤ 6 * n := by
  have := carry_sum c n
  rw [weight_zero] at this
  omega

/-! ### The fourteen-slot bank -/

/-- Slots zero to ten are the stage bank with blank replacement and output
slots and a zero pass index; slot eleven holds the source stream, slot twelve
the key tape, slot thirteen the counter with its head at position one. -/
def bank (k : ℕ) (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ)
    (src : ℤ → Fin 5) (hs : ℤ) (key ctr : ℤ → Fin 5) : Tapes 14 1 :=
  (stage k 0 raw h0 0 (fun _ => blank) 0 t9 h9 (fun _ => blank) 0).append
    (⟨fun i => if i = 0 then hs else if i = 1 then 0 else 1,
      fun i => if i = 0 then src else if i = 1 then key else ctr⟩ : Tapes 3 1)

/-- Flag copier tapes: source, key, output, extracted at slots 11, 12, 9, 0. -/
def flagPlacement : Fin (4 + 10) ≃ Fin 14 where
  toFun := fun i => if i = 0 then 11 else if i = 1 then 12 else if i = 2 then 9
    else if i = 3 then 0 else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 3
    else if i = 7 then 4 else if i = 8 then 5 else if i = 9 then 6 else if i = 10 then 7
    else if i = 11 then 8 else if i = 12 then 10 else 13
  invFun := fun i => if i = 11 then 0 else if i = 12 then 1 else if i = 9 then 2
    else if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 6
    else if i = 4 then 7 else if i = 5 then 8 else if i = 6 then 9 else if i = 7 then 10
    else if i = 8 then 11 else if i = 10 then 12 else 13
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- The counter acts on slot 13. -/
def ctrPlacement : Fin (1 + 13) ≃ Fin 14 where
  toFun := fun i => if i = 0 then 13 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 9 else if i = 11 then 10 else if i = 12 then 11 else 12
  invFun := fun i => if i = 13 then 0 else if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 9 then 10 else if i = 10 then 11 else if i = 11 then 12 else 13
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- The output head return acts on slot 9. -/
def outPlacement : Fin (1 + 13) ≃ Fin 14 where
  toFun := fun i => if i = 0 then 9 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 10 else if i = 11 then 11 else if i = 12 then 12 else 13
  invFun := fun i => if i = 9 then 0 else if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 10 then 10 else if i = 11 then 11 else if i = 12 then 12 else 13
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- The extracted head return acts on slot 0. -/
def extPlacement : Fin (1 + 13) ≃ Fin 14 := Equiv.refl _

def flagPart : Program 14 6 1 := reindex (extend FlagCopy.program 10) flagPlacement
def ctrPart : Program 14 3 1 :=
  reindex (extend (Alphabet.program encoding CounterTape.program) 13) ctrPlacement
def outReturn : Program 14 3 1 := reindex (extend MarkedReturn.program 13) outPlacement
def extReturn : Program 14 3 1 := reindex (extend MarkedReturn.program 13) extPlacement

theorem flag_bank (k : ℕ) (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ)
    (src : ℤ → Fin 5) (hs : ℤ) (key ctr : ℤ → Fin 5) (s : Fin 6) :
    ((FlagCopy.cfg src key t9 (KeyPartition.rawTape raw) hs 0 h9 h0 s).tapes.append
      (⟨fun i => if i = 9 then 1 else 0,
        fun i => if i = 0 then KeySelect.selector 0 else if i = 6 then KeySelect.selector k
          else if i = 7 then (fun _ => blank) else if i = 8 then (fun _ => blank)
          else if i = 9 then ctr else markedTape 0 []⟩ : Tapes 10 1)).reindex flagPlacement =
      bank k raw h0 t9 h9 src hs key ctr := by
  unfold FlagCopy.cfg Config.tapes Tapes.append Tapes.reindex bank stage flagPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem ctr_bank (k : ℕ) (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ)
    (src : ℤ → Fin 5) (hs : ℤ) (key : ℤ → Fin 5) (bs : List Bool) :
    ((Alphabet.mapTapes encoding (CounterTape.tapes GrowingCounter.emptyTape bs)).append
      (⟨fun i => if i = 0 then h0 else if i = 9 then h9 else if i = 11 then hs else 0,
        fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector 0
          else if i = 7 then KeySelect.selector k else if i = 8 then (fun _ => blank)
          else if i = 9 then t9 else if i = 10 then (fun _ => blank) else if i = 11 then src
          else if i = 12 then key else markedTape 0 []⟩ : Tapes 13 1)).reindex ctrPlacement =
      bank k raw h0 t9 h9 src hs key (ctrTape bs) := by
  unfold CounterTape.tapes Alphabet.mapTapes Tapes.append Tapes.reindex bank stage ctrPlacement
    ctrTape
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem out_bank (k : ℕ) (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ)
    (src : ℤ → Fin 5) (hs : ℤ) (key ctr : ℤ → Fin 5) (s : Fin 3) :
    ((MarkedReturn.cfg t9 h9 s).tapes.append
      (⟨fun i => if i = 0 then h0 else if i = 10 then hs else if i = 12 then 1 else 0,
        fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector 0
          else if i = 7 then KeySelect.selector k else if i = 8 then (fun _ => blank)
          else if i = 9 then (fun _ => blank) else if i = 10 then src
          else if i = 11 then key else if i = 12 then ctr else markedTape 0 []⟩ : Tapes 13 1)).reindex
        outPlacement =
      bank k raw h0 t9 h9 src hs key ctr := by
  unfold MarkedReturn.cfg Config.tapes Tapes.append Tapes.reindex bank stage outPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem ext_bank (k : ℕ) (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ)
    (src : ℤ → Fin 5) (hs : ℤ) (key ctr : ℤ → Fin 5) (s : Fin 3) :
    ((MarkedReturn.cfg (KeyPartition.rawTape raw) h0 s).tapes.append
      (⟨fun i => if i = 8 then h9 else if i = 10 then hs else if i = 12 then 1 else 0,
        fun i => if i = 0 then KeySelect.selector 0
          else if i = 6 then KeySelect.selector k else if i = 7 then (fun _ => blank)
          else if i = 8 then t9 else if i = 9 then (fun _ => blank) else if i = 10 then src
          else if i = 11 then key else if i = 12 then ctr else markedTape 0 []⟩ : Tapes 13 1)).reindex
        extPlacement =
      bank k raw h0 t9 h9 src hs key ctr := by
  unfold MarkedReturn.cfg Config.tapes Tapes.append Tapes.reindex bank stage extPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ### The scan states -/

section Scan

variable (k : ℕ) (records : List Record) (flag : ℕ → Bool) (bits : ℕ → List Bool) (c : ℕ)

/-- The blank-backed source stream. -/
def srcTape : ℤ → Fin 5 := putWord (fun _ => blank) 0 (DropFlag.encode records)

/-- A blank-backed flagged stream. -/
def outTape (rs : List Record) : ℤ → Fin 5 := putWord (fun _ => blank) 0 (DropFlag.encode rs)

theorem outTape_eq (rs : List Record) : outTape rs = encTape (Partition.encode rs) := by
  rw [outTape, DropFlag.encode_partition, RepairStage.encTape_eq]

/-- The bank after `j` records, with key word `key` and `n` counter increments. -/
def scanBank (j : ℕ) (key : List (Fin 5)) (n : ℕ) : Tapes 14 1 :=
  bank k (raw (items flag bits 0 (records.take j)))
    (KeySelect.encode (raw (items flag bits 0 (records.take j)))).length
    (outTape (flagged flag 0 (records.take j)))
    (DropFlag.encode (flagged flag 0 (records.take j))).length
    (srcTape records) (DropFlag.encode (records.take j)).length
    (FlagCopy.keyTape key) (ctrTape (counter c n))

theorem scanBank_zero :
    scanBank k records flag bits c 0 [] 0 =
      bank k [] 0 (fun _ => blank) 0 (srcTape records) 0 (FlagCopy.keyTape [])
        (ctrTape (List.replicate c false)) := by
  simp [scanBank, items, flagged, raw, outTape, DropFlag.encode, KeySelect.encode, counter,
    Counter.advance, putWord]

/-- The flag copier carries the bank over record `j`. -/
theorem flag_step (j : ℕ) (hj : j < records.length) :
    HoareTime flagPart
      (fun v => v = scanBank k records flag bits c j (FlagCopy.keyWord (flag j) (bits j)) j)
      (fun v => v = scanBank k records flag bits c (j + 1) [] j)
      (FlagCopy.cost (flag j) (bits j) records[j].payload) := by
  set r := records[j] with hr
  set A := DropFlag.encode (records.take j) with hA
  set w := DropFlag.recordWord r with hw
  set B := DropFlag.encode (records.drop (j + 1)) with hB
  have hsplit : records = records.take j ++ r :: records.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j records, List.drop_eq_getElem_cons hj]
  have htake : records.take (j + 1) = records.take j ++ [r] := (List.take_append_getElem hj).symm
  have hlen : (records.take j).length = j := List.length_take_of_le hj.le
  have hsrc : srcTape records =
      putWord (putWord (putWord (fun _ => blank) 0 A) (A.length + w.length) B) A.length w := by
    rw [srcTape]
    conv_lhs => rw [hsplit, dropFlag_encode_append, DropFlag.encode]
    rw [← putWord_append_forward, putWord_append, zero_add]
  have hout : outTape (flagged flag 0 (records.take (j + 1))) =
      putWord (outTape (flagged flag 0 (records.take j)))
        (DropFlag.encode (flagged flag 0 (records.take j))).length
        (DropFlag.recordWord ⟨flag j, r.payload⟩) := by
    have hf := putWord_append_forward (fun _ => (blank : Fin 5)) 0
      (DropFlag.encode (flagged flag 0 (records.take j))) (DropFlag.recordWord ⟨flag j, r.payload⟩)
    rw [zero_add] at hf
    rw [outTape, outTape, hf, htake, flagged_append, hlen, zero_add, dropFlag_encode_append]
    simp [flagged, DropFlag.encode]
  have hext : KeyPartition.rawTape (raw (items flag bits 0 (records.take (j + 1)))) =
      putWord (KeyPartition.rawTape (raw (items flag bits 0 (records.take j))))
        (KeySelect.encode (raw (items flag bits 0 (records.take j)))).length
        (FlagCopy.extractedWord (flag j) (bits j) r.payload) := by
    have hf := putWord_append_forward (markedTape 0 []) 0
      (KeySelect.encode (raw (items flag bits 0 (records.take j))))
      (FlagCopy.extractedWord (flag j) (bits j) r.payload)
    rw [zero_add] at hf
    rw [KeyPartition.rawTape, KeyPartition.rawTape, hf, htake, items_append,
      hlen, zero_add, raw, List.map_append, keySelect_encode_append, ← raw, ← raw, raw_items_single]
  have hwlen : (DropFlag.encode (records.take (j + 1))).length = A.length + (r.payload.length + 2) := by
    rw [htake, dropFlag_encode_append, List.length_append, hA]
    simp [DropFlag.encode, DropFlag.recordWord, KeySelect.recordWord]
  have hflen : (DropFlag.encode (flagged flag 0 (records.take (j + 1)))).length =
      (DropFlag.encode (flagged flag 0 (records.take j))).length + (r.payload.length + 2) := by
    rw [htake, flagged_append, hlen, zero_add, dropFlag_encode_append, List.length_append]
    simp [flagged, DropFlag.encode, DropFlag.recordWord, KeySelect.recordWord]
  have helen : (KeySelect.encode (raw (items flag bits 0 (records.take (j + 1))))).length =
      (KeySelect.encode (raw (items flag bits 0 (records.take j)))).length +
        (FlagCopy.extractedWord (flag j) (bits j) r.payload).length := by
    rw [htake, items_append, hlen, zero_add, raw, List.map_append, keySelect_encode_append,
      ← raw, ← raw, raw_items_single, List.length_append]
  have h := hoare_place (FlagCopy.record_hoare (flag j) r.key r.payload (bits j)
    (putWord (putWord (fun _ => blank) 0 A) (A.length + w.length) B)
    (outTape (flagged flag 0 (records.take j)))
    (KeyPartition.rawTape (raw (items flag bits 0 (records.take j)))) A.length
    (DropFlag.encode (flagged flag 0 (records.take j))).length
    (KeySelect.encode (raw (items flag bits 0 (records.take j)))).length) flagPlacement
    (⟨fun i => if i = 9 then 1 else 0,
      fun i => if i = 0 then KeySelect.selector 0 else if i = 6 then KeySelect.selector k
        else if i = 7 then (fun _ => blank) else if i = 8 then (fun _ => blank)
        else if i = 9 then ctrTape (counter c j) else markedTape 0 []⟩ : Tapes 10 1)
  rw [flag_bank, ← hext, flag_bank] at h
  refine h.consequence (fun v hv => ?_) (fun v hv => ?_) le_rfl
  · rw [hv, scanBank, hsrc]
  · rw [hv, scanBank, hsrc, hout, helen, hwlen, hflen]
    push_cast
    rfl

/-- The counter step carries the bank from `n` to `n + 1` increments. -/
theorem ctr_step (raw : List (List Bool)) (h0 : ℤ) (t9 : ℤ → Fin 5) (h9 : ℤ) (src : ℤ → Fin 5)
    (hs : ℤ) (key : ℤ → Fin 5) (n : ℕ) :
    HoareTime ctrPart
      (fun v => v = bank k raw h0 t9 h9 src hs key (ctrTape (counter c n)))
      (fun v => v = bank k raw h0 t9 h9 src hs key (ctrTape (counter c (n + 1))))
      (2 * CounterTape.carrySteps (counter c n)) := by
  have h := hoare_place (hoare_widen (CounterTape.increment_hoare GrowingCounter.emptyTape
    (counter c n) rfl (by simp [GrowingCounter.emptyTape]; intro h; omega))) ctrPlacement
    (⟨fun i => if i = 0 then h0 else if i = 9 then h9 else if i = 11 then hs else 0,
      fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector 0
        else if i = 7 then KeySelect.selector k else if i = 8 then (fun _ => blank)
        else if i = 9 then t9 else if i = 10 then (fun _ => blank) else if i = 11 then src
        else if i = 12 then key else markedTape 0 []⟩ : Tapes 13 1)
  rw [ctr_bank, ctr_bank, ← counter_succ] at h
  exact h

/-! ### The loop -/

variable (s : ℕ) {qK : ℕ} (K : Program (14 + s) qK 1) (cK : ℕ) (scratch : Tapes s 1)

/-- One iteration: key routine, flag copier, counter increment. -/
def body : Program (14 + s) (qK + 6 + 3) 1 := seq (seq K (extend flagPart s)) (extend ctrPart s)

/-- Continue while the source head reads a record. -/
def test : (Fin (14 + s) → Fin 5) → Bool := fun syms => decide (syms (Fin.castAdd s 11) ≠ blank)

def scan : Program (14 + s) (qK + 6 + 3 + 1) 1 := whileLoop (body s K) (test s)

/-- The key routine's contract: at rank `j`, write the flag and the
destination bits on the blank key tape, leaving every other tape and its own
scratch frame as they were. -/
def KeyContract : Prop := ∀ j < records.length,
  HoareTime K (fun v => v = (scanBank k records flag bits c j [] j).append scratch)
    (fun v => v = (scanBank k records flag bits c j (FlagCopy.keyWord (flag j) (bits j)) j).append
      scratch) cK

/-- The iteration cost at rank `j`, with the stored record's payload length. -/
def iterCost (j : ℕ) : ℕ :=
  cK + 1 + FlagCopy.cost (flag j) (bits j) (records.getD j ⟨false, []⟩).payload + 1 +
    2 * CounterTape.carrySteps (counter c j)

theorem body_hoare (hK : KeyContract k records flag bits c s K cK scratch) (j : ℕ)
    (hj : j < records.length) :
    HoareTime (body s K)
      (fun v => v = (scanBank k records flag bits c j [] j).append scratch)
      (fun v => v = (scanBank k records flag bits c (j + 1) [] (j + 1)).append scratch)
      (iterCost records flag bits c cK j) := by
  have hf := hoare_extend_eq (flag_step k records flag bits c j hj) scratch
  have hc := hoare_extend_eq (ctr_step k c (raw (items flag bits 0 (records.take (j + 1))))
    (KeySelect.encode (raw (items flag bits 0 (records.take (j + 1))))).length
    (outTape (flagged flag 0 (records.take (j + 1))))
    (DropFlag.encode (flagged flag 0 (records.take (j + 1)))).length (srcTape records)
    (DropFlag.encode (records.take (j + 1))).length (FlagCopy.keyTape []) j) scratch
  have := ((hK j hj).seq hf).seq hc
  rw [iterCost, List.getD_eq_getElem records _ hj]
  exact this

theorem bank_reads (v : Tapes 14 1) (extra : Tapes s 1) :
    (v.append extra).reads (Fin.castAdd s 11) = v.tape 11 (v.head 11) := by
  simp [Tapes.reads, Tapes.append]

theorem scanBank_src (j : ℕ) (key : List (Fin 5)) (n : ℕ) :
    (scanBank k records flag bits c j key n).tape 11 = srcTape records ∧
    (scanBank k records flag bits c j key n).head 11 = (DropFlag.encode (records.take j)).length := by
  constructor <;> rfl

theorem test_true (j : ℕ) (hj : j < records.length) (key : List (Fin 5)) (n : ℕ) :
    test s ((scanBank k records flag bits c j key n).append scratch).reads = true := by
  rw [test, bank_reads, (scanBank_src k records flag bits c j key n).1,
    (scanBank_src k records flag bits c j key n).2]
  have hsplit : records = records.take j ++ records[j] :: records.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j records, List.drop_eq_getElem_cons hj]
  have hsrc : srcTape records (DropFlag.encode (records.take j)).length =
      bitSymbol records[j].key := by
    have hf := putWord_append_forward (fun _ => (blank : Fin 5)) 0
      (DropFlag.encode (records.take j))
      (DropFlag.recordWord records[j] ++ DropFlag.encode (records.drop (j + 1)))
    rw [zero_add] at hf
    have henc : DropFlag.encode records = DropFlag.encode (records.take j) ++
        (DropFlag.recordWord records[j] ++ DropFlag.encode (records.drop (j + 1))) := by
      conv_lhs => rw [hsplit]
      rw [dropFlag_encode_append, DropFlag.encode]
    rw [srcTape, henc, ← hf, DropFlag.recordWord, List.cons_append, putWord_head]
  rw [hsrc]
  cases records[j].key <;> decide

theorem test_false (key : List (Fin 5)) (n : ℕ) :
    test s ((scanBank k records flag bits c records.length key n).append scratch).reads = false := by
  rw [test, bank_reads, (scanBank_src k records flag bits c _ key n).1,
    (scanBank_src k records flag bits c _ key n).2, List.take_length, srcTape,
    putWord_outside _ _ _ _ (Or.inr (by simp))]
  decide

/-- The complete scan: from the empty flagged and extracted streams and the
zero counter to the fully flagged stream, every extracted record in raw keyed
format, and the counter at the record count, with both written heads at the
end of their words. -/
theorem scan_hoare (hK : KeyContract k records flag bits c s K cK scratch) :
    HoareTime (scan s K)
      (fun v => v = (scanBank k records flag bits c 0 [] 0).append scratch)
      (fun v => v = (scanBank k records flag bits c records.length [] records.length).append
        scratch)
      (∑ j ∈ Finset.range records.length, (iterCost records flag bits c cK j + 2)) :=
  while_chain_hoare (body s K) (test s)
    (fun j => (scanBank k records flag bits c j [] j).append scratch) _ records.length
    (fun j hj => body_hoare k records flag bits c s K cK scratch hK j hj)
    (fun j hj => test_true k records flag bits c s scratch j hj [] j)
    (test_false k records flag bits c s scratch [] _)

end Scan

/-! ### The complete repair machine: scan, two head returns, stage -/

section Full

variable (k : ℕ) (records : List Record) (flag : ℕ → Bool) (bits : ℕ → List Bool) (c : ℕ)
variable (s : ℕ) {qK : ℕ} (K : Program (14 + s) qK 1) (cK : ℕ) (scratch : Tapes s 1)

/-- Scan, return the flagged-stream head, return the extracted-stream head,
then sort, strip, return and reinsert. -/
def program : Program (14 + s) (qK + 6 + 3 + 1 + 3 + 3 + (40 + 4 + 3 + 4)) 1 :=
  seq (seq (seq (scan s K) (extend outReturn s)) (extend extReturn s))
    (extend (extend RepairStage.program 3) s)

/-- The three scan slots after the scan: source head at its end, blank key
tape, counter at `n`. -/
def tail (n : ℕ) : Tapes 3 1 :=
  ⟨fun i => if i = 0 then ((DropFlag.encode records).length : ℤ) else if i = 1 then 0 else 1,
    fun i => if i = 0 then srcTape records else if i = 1 then FlagCopy.keyTape []
      else ctrTape (counter c n)⟩

theorem scanBank_full (key : List (Fin 5)) (n : ℕ) :
    scanBank k records flag bits c records.length key n =
      bank k (raw (items flag bits 0 records)) (KeySelect.encode (raw (items flag bits 0 records))).length
        (outTape (flagged flag 0 records)) (DropFlag.encode (flagged flag 0 records)).length
        (srcTape records) (DropFlag.encode records).length (FlagCopy.keyTape key)
        (ctrTape (counter c n)) := by
  unfold scanBank
  rw [List.take_length]

theorem out_step (raw : List (List Bool)) (h0 : ℤ) (rs : List Record) (src : ℤ → Fin 5) (hs : ℤ)
    (key ctr : ℤ → Fin 5) :
    HoareTime outReturn
      (fun v => v = bank k raw h0 (outTape rs) (DropFlag.encode rs).length src hs key ctr)
      (fun v => v = bank k raw h0 (outTape rs) 0 src hs key ctr)
      ((DropFlag.encode rs).length + 2) := by
  have h := hoare_place (MarkedReturn.return_hoare (fun _ => blank) 0 (DropFlag.encode rs)
    (MarkedReturn.dropFlag_interior rs) (by decide)) outPlacement
    (⟨fun i => if i = 0 then h0 else if i = 10 then hs else if i = 12 then 1 else 0,
      fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector 0
        else if i = 7 then KeySelect.selector k else if i = 8 then (fun _ => blank)
        else if i = 9 then (fun _ => blank) else if i = 10 then src
        else if i = 11 then key else if i = 12 then ctr else markedTape 0 []⟩ : Tapes 13 1)
  simp only [zero_add] at h
  rw [out_bank, out_bank] at h
  exact h

theorem ext_step (raw : List (List Bool)) (t9 : ℤ → Fin 5) (h9 : ℤ) (src : ℤ → Fin 5) (hs : ℤ)
    (key ctr : ℤ → Fin 5) :
    HoareTime extReturn
      (fun v => v = bank k raw (KeySelect.encode raw).length t9 h9 src hs key ctr)
      (fun v => v = bank k raw 0 t9 h9 src hs key ctr)
      ((KeySelect.encode raw).length + 2) := by
  have h := hoare_place (MarkedReturn.return_hoare (markedTape 0 []) 0 (KeySelect.encode raw)
    (MarkedReturn.keySelect_interior raw)
    (by rw [PartitionMarked.markedTape_marker]; decide)) extPlacement
    (⟨fun i => if i = 8 then h9 else if i = 10 then hs else if i = 12 then 1 else 0,
      fun i => if i = 0 then KeySelect.selector 0
        else if i = 6 then KeySelect.selector k else if i = 7 then (fun _ => blank)
        else if i = 8 then t9 else if i = 9 then (fun _ => blank) else if i = 10 then src
        else if i = 11 then key else if i = 12 then ctr else markedTape 0 []⟩ : Tapes 13 1)
  simp only [zero_add] at h
  have hraw : putWord (markedTape 0 []) 0 (KeySelect.encode raw) = KeyPartition.rawTape raw := rfl
  rw [hraw, ext_bank, ext_bank] at h
  exact h

theorem replacements_length :
    (RepairStage.replacements k (items flag bits 0 records)).length =
      Reinsert.holes (flagged flag 0 records) := by
  rw [RepairStage.replacements, List.length_map, RepairStage.sortedItems,
    (RadixSort.sort_perm _ _ _).length_eq, items_length]

/-- The stage bound in the form of `RepairStage.stage_hoare`. -/
def stageBound (its : List Keyed) (fl : List Record) : ℕ :=
  74 * k * (KeySelect.encode (raw its)).length + 1 +
    (TapeRadixSort.completed k (raw its) + 2 + ((KeySelect.encode (RepairStage.sortedRaw k its)).length +
      (RepairStage.sortedRaw k its).length * (k + 2))) + 1 +
    ((KeySelect.encode (StripPrefix.stripped k (RepairStage.sortedRaw k its))).length + 2) + 1 +
    ((Partition.encode fl).length + (Partition.encode (RepairStage.replacements k its)).length)

/-- The final stage bank: sorted raw records, stripped replacements, the
flagged stream, and the repaired output, each head at the end of its word. -/
def finalStage (its : List Keyed) (fl : List Record) : Tapes 11 1 :=
  stage k (TapeRadixSort.completed k (raw its)) (RepairStage.sortedRaw k its)
    (KeySelect.encode (RepairStage.sortedRaw k its)).length 0
    (encTape (Partition.encode (RepairStage.replacements k its)))
    (Partition.encode (RepairStage.replacements k its)).length
    (encTape (Partition.encode fl)) (Partition.encode fl).length
    (encTape (Partition.encode (Reinsert.fill fl (RepairStage.replacements k its))))
    (Partition.encode (Reinsert.fill fl (RepairStage.replacements k its))).length

/-- The complete contract: from the source stream, blank work slots and the
zero counter, the machine halts with the repaired stream on the output slot. -/
theorem program_hoare (hK : KeyContract k records flag bits c s K cK scratch)
    (hbits : ∀ j < records.length, (bits j).length = k) :
    HoareTime (program s K)
      (fun v => v = (scanBank k records flag bits c 0 [] 0).append scratch)
      (fun v => v = ((finalStage k (items flag bits 0 records) (flagged flag 0 records)).append
        (tail records c records.length)).append scratch)
      (∑ j ∈ Finset.range records.length, (iterCost records flag bits c cK j + 2) + 1 +
        ((DropFlag.encode (flagged flag 0 records)).length + 2) + 1 +
        ((KeySelect.encode (raw (items flag bits 0 records))).length + 2) + 1 +
        stageBound k (items flag bits 0 records) (flagged flag 0 records)) := by
  have hscan := scan_hoare k records flag bits c s K cK scratch hK
  rw [scanBank_full] at hscan
  have h1 := hoare_extend_eq (out_step k (raw (items flag bits 0 records))
    (KeySelect.encode (raw (items flag bits 0 records))).length (flagged flag 0 records)
    (srcTape records) (DropFlag.encode records).length (FlagCopy.keyTape [])
    (ctrTape (counter c records.length))) scratch
  have h2 := hoare_extend_eq (ext_step k (raw (items flag bits 0 records))
    (outTape (flagged flag 0 records)) 0 (srcTape records) (DropFlag.encode records).length
    (FlagCopy.keyTape []) (ctrTape (counter c records.length))) scratch
  have h3 := hoare_extend_eq (hoare_extend_eq (RepairStage.stage_hoare k (items flag bits 0 records)
    (items_keys flag bits k 0 records (fun i _ hi => hbits i (by simpa using hi)))
    (flagged flag 0 records) (replacements_length k records flag bits))
    (tail records c records.length)) scratch
  have h3' := h3.consequence (pre' := fun v => v = (bank k (raw (items flag bits 0 records)) 0
      (outTape (flagged flag 0 records)) 0 (srcTape records) (DropFlag.encode records).length
      (FlagCopy.keyTape []) (ctrTape (counter c records.length))).append scratch)
    (post' := fun v => v = ((finalStage k (items flag bits 0 records) (flagged flag 0 records)).append
      (tail records c records.length)).append scratch)
    (fun v hv => by rw [hv, outTape_eq]; rfl) (fun v hv => hv) le_rfl
  exact ((hscan.seq h1).seq h2).seq h3'

end Full

/-! ### Cost accounting -/

section Cost

def listSum (g : ℕ → Record → ℕ) : ℕ → List Record → ℕ
  | _, [] => 0
  | j, r :: rs => g j r + listSum g (j + 1) rs

theorem sum_range_getD (g : ℕ → Record → ℕ) (rs : List Record) (d : Record) :
    ∑ j ∈ Finset.range rs.length, g j (rs.getD j d) = listSum g 0 rs := by
  suffices h : ∀ i, ∑ j ∈ Finset.range rs.length, g (i + j) (rs.getD j d) = listSum g i rs by
    simpa using h 0
  induction rs with
  | nil => simp [listSum]
  | cons r rs ih =>
    intro i
    rw [List.length_cons, Finset.sum_range_succ', listSum, ← ih (i + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.add_assoc, Nat.add_right_comm]

theorem listSum_volume (i : ℕ) (rs : List Record) :
    listSum (fun _ r => r.payload.length + 2) i rs = (DropFlag.encode rs).length := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    simp only [listSum, ih, DropFlag.encode, DropFlag.recordWord, KeySelect.recordWord,
      List.length_append, List.length_cons, List.length_map, List.length_nil]

theorem listSum_flags (flag : ℕ → Bool) (bits : ℕ → List Bool) (k i : ℕ) (rs : List Record)
    (hbits : ∀ j, i ≤ j → j < i + rs.length → (bits j).length = k) :
    listSum (fun j _ => if flag j then 2 * (bits j).length + 3 else 0) i rs =
      (2 * k + 3) * Reinsert.holes (flagged flag i rs) := by
  induction rs generalizing i with
  | nil => simp [listSum, flagged]
  | cons r rs ih =>
    have hi := hbits i le_rfl (by simp)
    rw [listSum, ih (i + 1) (fun j hj hj' => hbits j (by omega) (by simp only [List.length_cons]; omega))]
    simp only [flagged, Reinsert.holes, List.filter_cons]
    cases flag i <;> simp [hi]
    all_goals ring

theorem encode_flagged_length (flag : ℕ → Bool) (i : ℕ) (rs : List Record) :
    (DropFlag.encode (flagged flag i rs)).length = (DropFlag.encode rs).length := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    simp [flagged, DropFlag.encode, DropFlag.recordWord, KeySelect.recordWord, ih]

variable (k : ℕ) (records : List Record) (flag : ℕ → Bool) (bits : ℕ → List Bool) (c cK : ℕ)

/-- The scan costs the key routine plus ten per record, the stream volume,
and `2k + 3` per extracted record. -/
theorem scan_cost_le (hbits : ∀ j < records.length, (bits j).length = k) :
    ∑ j ∈ Finset.range records.length, (iterCost records flag bits c cK j + 2) ≤
      records.length * (cK + 10) + (DropFlag.encode records).length +
        (2 * k + 3) * Reinsert.holes (flagged flag 0 records) := by
  have hsplit : ∀ j, iterCost records flag bits c cK j + 2 =
      (cK + 4) + ((records.getD j ⟨false, []⟩).payload.length + 2) +
        (if flag j then 2 * (bits j).length + 3 else 0) +
        2 * CounterTape.carrySteps (counter c j) := by
    intro j
    simp only [iterCost, FlagCopy.cost]
    omega
  have h1 := sum_range_getD (fun _ r => r.payload.length + 2) records ⟨false, []⟩
  have h2 := sum_range_getD (fun j _ => if flag j then 2 * (bits j).length + 3 else 0) records
    ⟨false, []⟩
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, h1, h2, listSum_volume, listSum_flags flag bits k 0 records
    (fun j _ hj => hbits j (by simpa using hj))]
  have h3 := carry_sum_le c records.length
  nlinarith

/-- The stage bound as a closed expression (`RepairStage.stage_cost_le`). -/
theorem stageBound_le (its : List Keyed) (fl : List Record) (hk : ∀ x ∈ its, x.1.length = k) :
    stageBound k its fl ≤
      (74 * k + 4) * (KeySelect.encode (raw its)).length + (Partition.encode fl).length + k + 7 :=
  RepairStage.stage_cost_le k its hk fl

/-- The complete repair machine's bound: the key routine plus ten per record,
three stream volumes, `74k + 5` extracted volumes, `2k + 3` per extracted
record, and `k + 14`. -/
theorem program_cost_le (hbits : ∀ j < records.length, (bits j).length = k) :
    ∑ j ∈ Finset.range records.length, (iterCost records flag bits c cK j + 2) + 1 +
        ((DropFlag.encode (flagged flag 0 records)).length + 2) + 1 +
        ((KeySelect.encode (raw (items flag bits 0 records))).length + 2) + 1 +
        stageBound k (items flag bits 0 records) (flagged flag 0 records) ≤
      records.length * (cK + 10) + 3 * (DropFlag.encode records).length +
        (74 * k + 5) * (KeySelect.encode (raw (items flag bits 0 records))).length +
        (2 * k + 3) * Reinsert.holes (flagged flag 0 records) + k + 14 := by
  have h1 := scan_cost_le k records flag bits c cK hbits
  have h2 := stageBound_le k (items flag bits 0 records) (flagged flag 0 records)
    (items_keys flag bits k 0 records (fun i _ hi => hbits i (by simpa using hi)))
  have h3 : (Partition.encode (flagged flag 0 records)).length = (DropFlag.encode records).length := by
    rw [← encode_flagged_length flag 0 records, DropFlag.encode_partition, List.length_map]
  have h4 := encode_flagged_length flag 0 records
  rw [h3] at h2
  rw [h4]
  nlinarith

end Cost

end IntegerMultBounds.Machine.RepairScan
