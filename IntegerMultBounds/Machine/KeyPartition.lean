import IntegerMultBounds.Machine.KeySelect
import IntegerMultBounds.Machine.PartitionPass

/-! A complete physically selected stable partition on six tapes. Key selection,
rewinding, stable bucket routing, and concatenation are all literal programs;
the finite control is independent of the key index and record count. The input
must already carry a unary selector and marked blank work buffers. -/

namespace IntegerMultBounds.Machine.KeyPartition

open PartitionMarked

def selected (k : ℕ) (records : List (List Bool)) : List Partition.Record :=
  records.map (fun bits => ⟨KeySelect.keyAt k bits, bits⟩)

def flagWord (k : ℕ) (records : List (List Bool)) : List (Fin 4) :=
  Partition.encode (selected k records)

def rawTape (records : List (List Bool)) : ℤ → Fin 5 :=
  putWord (markedTape 0 []) 0 (KeySelect.encode records)

/-- Physical order: raw input, selector, flags, false bucket, true bucket, output.
The selector head is always restored to zero at phase boundaries. -/
def bank (k : ℕ) (records : List (List Bool)) (flags zeros ones out : List (Fin 4))
    (h₀ hF hZ hO hOut : ℤ) : Tapes 6 1 where
  head := fun i => if i = 0 then h₀ else if i = 1 then 0 else if i = 2 then hF
    else if i = 3 then hZ else if i = 4 then hO else hOut
  tape := fun i => if i = 0 then rawTape records else if i = 1 then KeySelect.selector k
    else if i = 2 then markedTape 0 flags else if i = 3 then markedTape 0 zeros
    else if i = 4 then markedTape 0 ones else markedTape 0 out

private def emptyThree : Tapes 3 1 := ⟨fun _ => 0, fun _ => markedTape 0 []⟩
private def emptyTwo : Tapes 2 1 := ⟨fun _ => 0, fun _ => markedTape 0 []⟩

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

private theorem empty_after (n : ℕ) : markedTape 0 [] n = blank := by
  have hn : (n : ℤ) ≠ 0 - 1 := by omega
  simp only [markedTape, hn, ↓reduceIte, putWord]
  rfl

private theorem select_bank (k : ℕ) (records : List (List Bool)) (flags : List (Fin 4))
    (h₀ hF : ℤ) :
    (KeySelect.cfg (rawTape records) (KeySelect.selector k) (markedTape 0 flags) h₀ 0 hF 0).tapes.append
      emptyThree = bank k records flags [] [] [] h₀ hF 0 0 0 := by
  unfold Config.tapes KeySelect.cfg Tapes.append bank emptyThree
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def selectionTime (k : ℕ) (records : List (List Bool)) : ℕ :=
  (KeySelect.encode records).length + records.length * (2 * k + 2)

private theorem selection_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ExactRun (extend KeySelect.program 3) (selectionTime k records)
      (bank k records [] [] [] [] 0 0 0 0 0)
      (bank k records (flagWord k records) [] [] [] (KeySelect.encode records).length
        (flagWord k records).length 0 0 0) := by
  obtain ⟨hr, hh⟩ := KeySelect.stream_exact k records hvalid (markedTape 0 []) (markedTape 0 [])
    0 0 (by simpa only [zero_add] using empty_after (KeySelect.encode records).length)
  have hw : putWord (markedTape 0 []) 0 (KeySelect.flagged k records) =
      markedTape 0 (flagWord k records) := by
    rw [KeySelect.flagged_partition, ← markedTape_putWord]
    rfl
  have hlen : (KeySelect.flagged k records).length = (flagWord k records).length := by
    rw [KeySelect.flagged_partition, List.length_map]
    rfl
  simp only [hw, hlen, zero_add] at hr hh
  have hrun := extend_run KeySelect.program emptyThree hr
  have hhalt := extend_halt KeySelect.program emptyThree hh
  have hbefore :
      (KeySelect.cfg (rawTape records) (KeySelect.selector k) (markedTape 0 []) 0 0 0 0).extend
        emptyThree = (bank k records [] [] [] [] 0 0 0 0 0).start (extend KeySelect.program 3) := by
    have ht := select_bank k records [] 0 0
    unfold Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  change run (extend KeySelect.program 3) (selectionTime k records)
    ((KeySelect.cfg (rawTape records) (KeySelect.selector k) (markedTape 0 []) 0 0 0 0).extend
      emptyThree) = _ at hrun
  rw [hbefore] at hrun
  exact ⟨_, hrun, hhalt, select_bank k records (flagWord k records)
    (KeySelect.encode records).length (flagWord k records).length⟩

private def resetView (k : ℕ) (records : List (List Bool)) (flags : List (Fin 4))
    (h₀ hF : ℤ) : Tapes 4 1 where
  head := fun i => if i = 0 then h₀ else if i = 1 then 0 else if i = 2 then hF else 0
  tape := fun i => if i = 0 then rawTape records else if i = 1 then KeySelect.selector k
    else if i = 2 then markedTape 0 flags else markedTape 0 []

private theorem reset_bank (k : ℕ) (records : List (List Bool)) (flags : List (Fin 4))
    (h₀ hF : ℤ) :
    (resetView k records flags h₀ hF).append emptyTwo = bank k records flags [] [] [] h₀ hF 0 0 0 := by
  unfold resetView Tapes.append emptyTwo bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem reset_exact (k : ℕ) (records : List (List Bool)) (flags : List (Fin 4)) (h₀ : ℤ) :
    ExactRun (extend (PartitionPass.reset 2) 2) (flags.length + 2)
      (bank k records flags [] [] [] h₀ flags.length 0 0 0)
      (bank k records flags [] [] [] h₀ 0 0 0 0) := by
  obtain ⟨hr, hh⟩ := PartitionPass.reset_exact (resetView k records flags h₀ flags.length) 2 0 flags
    flags.length rfl (by change (flags.length : ℤ) = 0 + flags.length; omega)
  have hrun := extend_run (PartitionPass.reset 2) emptyTwo hr
  have hhalt := extend_halt (PartitionPass.reset 2) emptyTwo hh
  have hbefore :
      ((resetView k records flags h₀ flags.length).start (PartitionPass.reset 2)).extend emptyTwo =
        (bank k records flags [] [] [] h₀ flags.length 0 0 0).start
          (extend (PartitionPass.reset 2) 2) := by
    have ht := reset_bank k records flags h₀ flags.length
    unfold Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  change (Tapes.append
    ⟨Function.update (resetView k records flags h₀ flags.length).head 2 0,
      (resetView k records flags h₀ flags.length).tape⟩ emptyTwo) = _
  rw [← reset_bank k records flags h₀ 0]
  congr 1
  unfold resetView
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Move the partition pass to tapes two through five; its two extra tapes
preserve the original raw stream and selector in physical slots zero and one. -/
def passPlacement : Fin 6 ≃ Fin 6 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4
    else if i = 3 then 5 else if i = 4 then 0 else 1
  invFun := fun i => if i = 0 then 4 else if i = 1 then 5 else if i = 2 then 0
    else if i = 3 then 1 else if i = 4 then 2 else 3
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def partitionProgram : Program 6 9 1 :=
  reindex (extend PartitionPass.program 2) passPlacement

private def protectedTapes (k : ℕ) (records : List (List Bool)) (h₀ : ℤ) : Tapes 2 1 where
  head := fun i => if i = 0 then h₀ else 0
  tape := fun i => if i = 0 then rawTape records else KeySelect.selector k

private theorem partition_bank (k : ℕ) (records : List (List Bool))
    (flags zeros ones out : List (Fin 4)) (h₀ hF hZ hO hOut : ℤ) :
    ((PartitionPass.bank flags zeros ones out hF hZ hO hOut).append
      (protectedTapes k records h₀)).reindex passPlacement =
      bank k records flags zeros ones out h₀ hF hZ hO hOut := by
  unfold PartitionPass.bank PartitionMarked.cfg Config.tapes Tapes.append Tapes.reindex
    protectedTapes bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem partition_exact (k : ℕ) (records : List (List Bool)) (h₀ : ℤ) :
    ExactRun partitionProgram (3 * (flagWord k records).length + 8)
      (bank k records (flagWord k records) [] [] [] h₀ 0 0 0 0)
      (bank k records (flagWord k records)
        (Partition.bucket false (selected k records)) (Partition.bucket true (selected k records))
        (Partition.encode (RadixSort.pass Partition.Record.key (selected k records))) h₀
        (flagWord k records).length (Partition.bucket false (selected k records)).length
        (Partition.bucket true (selected k records)).length (flagWord k records).length) := by
  obtain ⟨c, hr, hh, hc⟩ := PartitionPass.pass_stable_exact (selected k records)
  have hrun := reindex_run (extend PartitionPass.program 2) passPlacement
    (extend_run PartitionPass.program (protectedTapes k records h₀) hr)
  have hhalt := reindex_halt (extend PartitionPass.program 2) passPlacement
    (extend_halt PartitionPass.program (protectedTapes k records h₀) hh)
  have hbefore :
      (((PartitionPass.bank (flagWord k records) [] [] [] 0 0 0 0).start PartitionPass.program).extend
        (protectedTapes k records h₀)).reindex passPlacement =
      (bank k records (flagWord k records) [] [] [] h₀ 0 0 0 0).start partitionProgram := by
    have ht := partition_bank k records (flagWord k records) [] [] [] h₀ 0 0 0 0
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  change run partitionProgram (3 * (flagWord k records).length + 8)
    ((((PartitionPass.bank (flagWord k records) [] [] [] 0 0 0 0).start PartitionPass.program).extend
      (protectedTapes k records h₀)).reindex passPlacement) = _ at hrun
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  change (c.tapes.append (protectedTapes k records h₀)).reindex passPlacement = _
  rw [hc]
  exact partition_bank k records _ _ _ _ h₀ _ _ _ _

/-- Fixed finite program: key selection, flagged-stream reset, then stable pass. -/
def program : Program 6 15 1 :=
  seq (seq (extend KeySelect.program 3) (extend (PartitionPass.reset 2) 2)) partitionProgram

def runtime (k : ℕ) (records : List (List Bool)) : ℕ :=
  selectionTime k records + 4 * (flagWord k records).length + 12

/-- Whole-tape exact execution at an arbitrary valid key index. All joins and
rewinds are included; the raw source, selector, and marked source flags survive. -/
theorem pass_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ∃ c, run program (runtime k records)
      ((bank k records [] [] [] [] 0 0 0 0 0).start program) = some c ∧
      step program c = none ∧ c.tapes =
        bank k records (flagWord k records)
          (Partition.bucket false (selected k records)) (Partition.bucket true (selected k records))
          (Partition.encode (RadixSort.pass Partition.Record.key (selected k records)))
          (KeySelect.encode records).length (flagWord k records).length
          (Partition.bucket false (selected k records)).length
          (Partition.bucket true (selected k records)).length (flagWord k records).length := by
  have hs := selection_exact k records hvalid
  have hr := reset_exact k records (flagWord k records) (KeySelect.encode records).length
  have hp := partition_exact k records (KeySelect.encode records).length
  have ht := exact_seq (exact_seq hs hr) hp
  have hcost : selectionTime k records + 1 + ((flagWord k records).length + 2) + 1 +
      (3 * (flagWord k records).length + 8) = runtime k records := by unfold runtime; omega
  simpa only [hcost, program, ExactRun] using ht

theorem pass_hoare (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    HoareTime program
      (fun v => v = bank k records [] [] [] [] 0 0 0 0 0)
      (fun v => v = bank k records (flagWord k records)
        (Partition.bucket false (selected k records)) (Partition.bucket true (selected k records))
        (Partition.encode (RadixSort.pass Partition.Record.key (selected k records)))
        (KeySelect.encode records).length (flagWord k records).length
        (Partition.bucket false (selected k records)).length
        (Partition.bucket true (selected k records)).length (flagWord k records).length)
      (runtime k records) := by
  rintro v rfl
  obtain ⟨c, hr, hh, hc⟩ := pass_exact k records hvalid
  exact ⟨_, c, le_rfl, hr, hh, hc⟩

/-- Adding the selected flag commutes with the stable partition of original
records. Payloads, duplicates, and their order are carried through unchanged. -/
theorem selected_pass (k : ℕ) (records : List (List Bool)) :
    RadixSort.pass Partition.Record.key (selected k records) =
      selected k (RadixSort.pass (KeySelect.keyAt k) records) := by
  simp only [RadixSort.pass, selected, List.filter_map, List.map_append, Function.comp_def]

/-- The final flagged stream represents exactly the list-level stable pass at
the chosen key position, not merely a partition of unrelated routing flags. -/
theorem pass_stable_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ∃ c, run program (runtime k records)
      ((bank k records [] [] [] [] 0 0 0 0 0).start program) = some c ∧
      step program c = none ∧ c.tapes =
        bank k records (flagWord k records)
          (Partition.bucket false (selected k records)) (Partition.bucket true (selected k records))
          (flagWord k (RadixSort.pass (KeySelect.keyAt k) records))
          (KeySelect.encode records).length (flagWord k records).length
          (Partition.bucket false (selected k records)).length
          (Partition.bucket true (selected k records)).length (flagWord k records).length := by
  simpa only [selected_pass, flagWord] using pass_exact k records hvalid

theorem flagWord_length (k : ℕ) (records : List (List Bool)) :
    (flagWord k records).length = (KeySelect.encode records).length + records.length := by
  have h := KeySelect.flagged_length k records
  rw [KeySelect.flagged_partition, List.length_map] at h
  exact h

/-- All positioning and dispatch work remains linear in the raw encoded volume.
The constant is uniform in the key position and number of records. -/
theorem runtime_le_linear (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    runtime k records ≤ 11 * (KeySelect.encode records).length + 12 := by
  have hs := KeySelect.runtime_le_three_volume k records hvalid
  have hi := KeySelect.index_volume k records hvalid
  have hr : records.length ≤ (KeySelect.encode records).length := by nlinarith
  unfold runtime selectionTime
  rw [flagWord_length]
  omega

end IntegerMultBounds.Machine.KeyPartition
