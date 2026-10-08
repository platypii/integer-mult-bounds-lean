import IntegerMultBounds.Machine.KeyPartition
import IntegerMultBounds.Machine.DropFlag

/-! A complete stable pass on raw records. Seven fixed tapes hold the original
raw input, selector, partition workspace, and a distinct raw output. The sorted
routing flags are destructively removed, and their emptied tape is rewound.
All joins, rewinds, erasure, and copying are charged as real transitions. -/

namespace IntegerMultBounds.Machine.KeyPass

open PartitionMarked

def sorted (k : ℕ) (records : List (List Bool)) : List (List Bool) :=
  RadixSort.pass (KeySelect.keyAt k) records

/-- Add a distinct seventh tape for the new raw stream; the old raw source is
never used as a destination or implicitly cleared. -/
def bank (k : ℕ) (records : List (List Bool)) (flags zeros ones sortedFlags : List (Fin 4))
    (output : List (List Bool)) (h₀ hF hZ hO hSorted hOut : ℤ) : Tapes 7 1 :=
  (KeyPartition.bank k records flags zeros ones sortedFlags h₀ hF hZ hO hSorted).append
    (⟨fun _ => hOut, fun _ => KeyPartition.rawTape output⟩ : Tapes 1 1)

private def ExactRun {t q a : ℕ} (M : Program t q a) (n : ℕ) (v w : Tapes t a) : Prop :=
  ∃ c, run M n (v.start M) = some c ∧ step M c = none ∧ c.tapes = w

private theorem exact_seq {t q r a : ℕ} {M : Program t q a} {N : Program t r a}
    {k l : ℕ} {v w z : Tapes t a} (hm : ExactRun M k v w) (hn : ExactRun N l w z) :
    ExactRun (seq M N) (k + 1 + l) v z := by
  obtain ⟨c, hr, hh, hc⟩ := hm
  obtain ⟨d, hs, hd, he⟩ := hn
  refine ⟨d.mapState (Fin.natAdd q), ?_, seq_halt_right M N hd, he⟩
  rw [← hc] at hs
  exact seq_run M N hr hh hs

/-- The stable permutation preserves flagged and raw stream volumes. -/
theorem sorted_flags_length (k : ℕ) (records : List (List Bool)) :
    (KeyPartition.flagWord k (sorted k records)).length = (KeyPartition.flagWord k records).length := by
  unfold KeyPartition.flagWord sorted
  rw [← KeyPartition.selected_pass, ← Partition.buckets_eq_pass, List.length_append,
    Partition.bucket_lengths]

theorem sorted_raw_length (k : ℕ) (records : List (List Bool)) :
    (KeySelect.encode (sorted k records)).length = (KeySelect.encode records).length := by
  have hf := sorted_flags_length k records
  rw [KeyPartition.flagWord_length, KeyPartition.flagWord_length] at hf
  have hn : (sorted k records).length = records.length := RadixSort.pass_length _ _
  omega

private theorem partition_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ExactRun (extend KeyPartition.program 1) (KeyPartition.runtime k records)
      (bank k records [] [] [] [] [] 0 0 0 0 0 0)
      (bank k records (KeyPartition.flagWord k records)
        (Partition.bucket false (KeyPartition.selected k records))
        (Partition.bucket true (KeyPartition.selected k records))
        (KeyPartition.flagWord k (sorted k records)) []
        (KeySelect.encode records).length (KeyPartition.flagWord k records).length
        (Partition.bucket false (KeyPartition.selected k records)).length
        (Partition.bucket true (KeyPartition.selected k records)).length
        (KeyPartition.flagWord k records).length 0) := by
  obtain ⟨c, hr, hh, hc⟩ := KeyPartition.pass_stable_exact k records hvalid
  let extra : Tapes 1 1 := ⟨fun _ => 0, fun _ => KeyPartition.rawTape []⟩
  refine ⟨c.extend extra, extend_run KeyPartition.program extra hr,
    extend_halt KeyPartition.program extra hh, ?_⟩
  change c.tapes.append extra = _
  rw [hc]
  rfl

private def updateHead (v : Tapes 7 1) (i : Fin 7) (p : ℤ) : Tapes 7 1 :=
  ⟨Function.update v.head i p, v.tape⟩

private def resetPlacement : Fin 7 ≃ Fin 7 := Equiv.swap 0 5

/-- The reset's active tape occupies slot five, the sorted-flag buffer. -/
def resetProgram : Program 7 2 1 :=
  reindex (extend (PartitionPass.reset 0) 3) resetPlacement

private def resetSmall (v : Tapes 7 1) : Tapes 4 1 where
  head := fun i => v.head (if i = 0 then 5 else Fin.castAdd 3 i)
  tape := fun i => v.tape (if i = 0 then 5 else Fin.castAdd 3 i)

private def resetExtra (v : Tapes 7 1) : Tapes 3 1 where
  head := fun i => v.head (if i = 0 then 4 else if i = 1 then 0 else 6)
  tape := fun i => v.tape (if i = 0 then 4 else if i = 1 then 0 else 6)

private theorem reset_view (v : Tapes 7 1) :
    ((resetSmall v).append (resetExtra v)).reindex resetPlacement = v := by
  cases v with | mk heads tapes =>
    unfold resetSmall resetExtra Tapes.append Tapes.reindex
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

/-- Reset the sorted-flag tape at exact cost, preserving every other head/cell. -/
private theorem reset_exact (v : Tapes 7 1) (word : List (Fin 4)) (distance : ℕ)
    (htape : v.tape 5 = markedTape 0 word) (hhead : v.head 5 = distance) :
    ExactRun resetProgram (distance + 2) v (updateHead v 5 0) := by
  obtain ⟨hr, hh⟩ := PartitionPass.reset_exact (resetSmall v) 0 0 word distance htape
    (by change v.head 5 = 0 + distance; simpa only [zero_add] using hhead)
  have hrun := reindex_run (extend (PartitionPass.reset 0) 3) resetPlacement
    (extend_run (PartitionPass.reset 0) (resetExtra v) hr)
  have hhalt := reindex_halt (extend (PartitionPass.reset 0) 3) resetPlacement
    (extend_halt (PartitionPass.reset 0) (resetExtra v) hh)
  have hbefore : (((resetSmall v).start (PartitionPass.reset 0)).extend (resetExtra v)).reindex
      resetPlacement = v.start resetProgram := by
    have ht := reset_view v
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  change (Tapes.append ⟨Function.update (resetSmall v).head 0 0, (resetSmall v).tape⟩
    (resetExtra v)).reindex resetPlacement = updateHead v 5 0
  unfold resetSmall resetExtra Tapes.append Tapes.reindex updateHead
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem update_bank (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sortedFlags : List (Fin 4)) (h₀ hF hZ hO hSorted hOut : ℤ) :
    updateHead (bank k records flags zeros ones sortedFlags output h₀ hF hZ hO hSorted hOut) 5 0 =
      bank k records flags zeros ones sortedFlags output h₀ hF hZ hO 0 hOut := by
  unfold updateHead bank KeyPartition.bank Tapes.append
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem reset_bank (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sortedFlags : List (Fin 4)) (h₀ hF hZ hO hOut : ℤ) (distance : ℕ) :
    ExactRun resetProgram (distance + 2)
      (bank k records flags zeros ones sortedFlags output h₀ hF hZ hO distance hOut)
      (bank k records flags zeros ones sortedFlags output h₀ hF hZ hO 0 hOut) := by
  have h := reset_exact (bank k records flags zeros ones sortedFlags output h₀ hF hZ hO distance hOut)
    sortedFlags distance rfl rfl
  simpa only [update_bank] using h

/-- DropFlag occupies sorted flags in slot five and new raw output in slot six. -/
def dropPlacement : Fin 7 ≃ Fin 7 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 0
    else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else 4
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4
    else if i = 3 then 5 else if i = 4 then 6 else if i = 5 then 0 else 1
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def dropProgram : Program 7 2 1 := reindex (extend (DropFlag.program true) 5) dropPlacement

private def dropExtra (k : ℕ) (records : List (List Bool)) (flags zeros ones : List (Fin 4))
    (h₀ hF hZ hO : ℤ) : Tapes 5 1 where
  head := fun i => if i = 0 then h₀ else if i = 1 then 0 else if i = 2 then hF
    else if i = 3 then hZ else hO
  tape := fun i => if i = 0 then KeyPartition.rawTape records else if i = 1 then KeySelect.selector k
    else if i = 2 then markedTape 0 flags else if i = 3 then markedTape 0 zeros else markedTape 0 ones

private theorem drop_bank (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sortedFlags : List (Fin 4)) (h₀ hF hZ hO hSorted hOut : ℤ) :
    ((DropFlag.cfg (markedTape 0 sortedFlags) (KeyPartition.rawTape output) hSorted hOut 0).tapes.append
      (dropExtra k records flags zeros ones h₀ hF hZ hO)).reindex dropPlacement =
      bank k records flags zeros ones sortedFlags output h₀ hF hZ hO hSorted hOut := by
  unfold DropFlag.cfg Config.tapes Tapes.append Tapes.reindex dropExtra bank KeyPartition.bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem drop_exact (k : ℕ) (records : List (List Bool))
    (flags zeros ones : List (Fin 4)) (h₀ hF hZ hO : ℤ) :
    ExactRun dropProgram (KeyPartition.flagWord k (sorted k records)).length
      (bank k records flags zeros ones (KeyPartition.flagWord k (sorted k records)) [] h₀ hF hZ hO 0 0)
      (bank k records flags zeros ones [] (sorted k records) h₀ hF hZ hO
        (KeyPartition.flagWord k (sorted k records)).length (KeySelect.encode (sorted k records)).length) := by
  obtain ⟨hr, hh⟩ := DropFlag.marked_exact (KeyPartition.selected k (sorted k records)) 0 0
  have hword : (DropFlag.encode (KeyPartition.selected k (sorted k records))).length =
      (KeyPartition.flagWord k (sorted k records)).length := by
    rw [DropFlag.encode_partition, List.length_map]
    rfl
  have hpayload : (KeyPartition.selected k (sorted k records)).map Partition.Record.payload =
      sorted k records := by simp [KeyPartition.selected, Function.comp_def]
  simp only [hword, hpayload, zero_add] at hr hh
  let extra := dropExtra k records flags zeros ones h₀ hF hZ hO
  have hrun := reindex_run (extend (DropFlag.program true) 5) dropPlacement
    (extend_run (DropFlag.program true) extra hr)
  have hhalt := reindex_halt (extend (DropFlag.program true) 5) dropPlacement
    (extend_halt (DropFlag.program true) extra hh)
  have hbefore :
      ((DropFlag.cfg (markedTape 0 (KeyPartition.flagWord k (sorted k records)))
        (KeyPartition.rawTape []) 0 0 0).extend extra).reindex dropPlacement =
      (bank k records flags zeros ones (KeyPartition.flagWord k (sorted k records)) [] h₀ hF hZ hO 0 0).start
        dropProgram := by
    have ht := drop_bank k records [] flags zeros ones (KeyPartition.flagWord k (sorted k records))
      h₀ hF hZ hO 0 0
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  change run dropProgram (KeyPartition.flagWord k (sorted k records)).length
    (((DropFlag.cfg (markedTape 0 (KeyPartition.flagWord k (sorted k records)))
      (KeyPartition.rawTape []) 0 0 0).extend extra).reindex dropPlacement) = _ at hrun
  rw [hbefore] at hrun
  exact ⟨_, hrun, hhalt, drop_bank k records (sorted k records) flags zeros ones [] h₀ hF hZ hO
    (KeyPartition.flagWord k (sorted k records)).length (KeySelect.encode (sorted k records)).length⟩

/-- One fixed program performs a stable raw-record pass and empties its temporary
sorted-flag buffer. Other old input/work tapes are retained explicitly. -/
def program : Program 7 21 1 :=
  seq (seq (seq (extend KeyPartition.program 1) resetProgram) dropProgram) resetProgram

def runtime (k : ℕ) (records : List (List Bool)) : ℕ :=
  KeyPartition.runtime k records + 3 * (KeyPartition.flagWord k records).length + 7

/-- Actual raw stable pass, including flag deletion and empty-buffer rewind. -/
theorem pass_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ∃ c, run program (runtime k records)
      ((bank k records [] [] [] [] [] 0 0 0 0 0 0).start program) = some c ∧
      step program c = none ∧ c.tapes =
        bank k records (KeyPartition.flagWord k records)
          (Partition.bucket false (KeyPartition.selected k records))
          (Partition.bucket true (KeyPartition.selected k records)) [] (sorted k records)
          (KeySelect.encode records).length (KeyPartition.flagWord k records).length
          (Partition.bucket false (KeyPartition.selected k records)).length
          (Partition.bucket true (KeyPartition.selected k records)).length 0 (KeySelect.encode records).length := by
  have hp := partition_exact k records hvalid
  have hr := reset_bank k records [] (KeyPartition.flagWord k records)
    (Partition.bucket false (KeyPartition.selected k records))
    (Partition.bucket true (KeyPartition.selected k records))
    (KeyPartition.flagWord k (sorted k records)) (KeySelect.encode records).length
    (KeyPartition.flagWord k records).length
    (Partition.bucket false (KeyPartition.selected k records)).length
    (Partition.bucket true (KeyPartition.selected k records)).length 0 (KeyPartition.flagWord k records).length
  have hd := drop_exact k records (KeyPartition.flagWord k records)
    (Partition.bucket false (KeyPartition.selected k records))
    (Partition.bucket true (KeyPartition.selected k records))
    (KeySelect.encode records).length (KeyPartition.flagWord k records).length
    (Partition.bucket false (KeyPartition.selected k records)).length
    (Partition.bucket true (KeyPartition.selected k records)).length
  simp only [sorted_flags_length, sorted_raw_length] at hd
  have he := reset_bank k records (sorted k records) (KeyPartition.flagWord k records)
    (Partition.bucket false (KeyPartition.selected k records))
    (Partition.bucket true (KeyPartition.selected k records)) [] (KeySelect.encode records).length
    (KeyPartition.flagWord k records).length
    (Partition.bucket false (KeyPartition.selected k records)).length
    (Partition.bucket true (KeyPartition.selected k records)).length (KeySelect.encode records).length
    (KeyPartition.flagWord k records).length
  have ht := exact_seq (exact_seq (exact_seq hp hr) hd) he
  have hcost : KeyPartition.runtime k records + 1 + ((KeyPartition.flagWord k records).length + 2) + 1 +
      (KeyPartition.flagWord k records).length + 1 + ((KeyPartition.flagWord k records).length + 2) =
      runtime k records := by unfold runtime; omega
  simpa only [hcost, program, ExactRun] using ht

theorem pass_hoare (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    HoareTime program
      (fun v => v = bank k records [] [] [] [] [] 0 0 0 0 0 0)
      (fun v => v = bank k records (KeyPartition.flagWord k records)
        (Partition.bucket false (KeyPartition.selected k records))
        (Partition.bucket true (KeyPartition.selected k records)) [] (sorted k records)
        (KeySelect.encode records).length (KeyPartition.flagWord k records).length
        (Partition.bucket false (KeyPartition.selected k records)).length
        (Partition.bucket true (KeyPartition.selected k records)).length 0 (KeySelect.encode records).length)
      (runtime k records) := by
  rintro v rfl
  obtain ⟨c, hr, hh, hc⟩ := pass_exact k records hvalid
  exact ⟨_, c, le_rfl, hr, hh, hc⟩

/-- The uniform linear bound includes every extra positioning and cleanup step. -/
theorem runtime_le_linear (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    runtime k records ≤ 17 * (KeySelect.encode records).length + 19 := by
  have hp := KeyPartition.runtime_le_linear k records hvalid
  have hi := KeySelect.index_volume k records hvalid
  have hr : records.length ≤ (KeySelect.encode records).length := by nlinarith
  unfold runtime
  rw [KeyPartition.flagWord_length]
  omega

end IntegerMultBounds.Machine.KeyPass
