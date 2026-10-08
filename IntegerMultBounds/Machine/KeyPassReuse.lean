import IntegerMultBounds.Machine.KeyPass
import IntegerMultBounds.Machine.Erase

/-! A physically reusable raw-key pass. Obsolete source and bucket streams are
cleared, the new raw stream is moved back into the original input tape, and all
heads return to their initial positions. Tape permutations only place finite
subroutines; no step is credited for a mathematical swap of tape contents. -/

namespace IntegerMultBounds.Machine.KeyPassReuse

open PartitionMarked

def rawWord : List (List Bool) → List (Fin 4)
  | [] => []
  | bits :: rest => (bits.map bitSymbol ++ [separator]) ++ rawWord rest

theorem rawWord_encode (records : List (List Bool)) :
    (rawWord records).map encoding.encode = KeySelect.encode records := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
    simp only [rawWord, KeySelect.encode, KeySelect.recordWord, List.map_append,
      List.map_map, ih]
    rfl

theorem rawWord_length (records : List (List Bool)) :
    (rawWord records).length = (KeySelect.encode records).length := by
  rw [← rawWord_encode, List.length_map]

theorem rawTape_marked (records : List (List Bool)) :
    KeyPartition.rawTape records = markedTape 0 (rawWord records) := by
  unfold KeyPartition.rawTape
  rw [← rawWord_encode, ← markedTape_putWord]

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

private def clean (v : Tapes 7 1) (i : Fin 7) : Tapes 7 1 :=
  ⟨Function.update v.head i 0, Function.update v.tape i (markedTape 0 [])⟩

private def positioned (v : Tapes 7 1) (i : Fin 7) : Tapes 7 1 :=
  ⟨Function.update v.head i 0, v.tape⟩

private def place (i : Fin 7) : Fin 7 ≃ Fin 7 := Equiv.swap 0 i

def eraseProgram (i : Fin 7) : Program 7 2 1 := reindex (extend Erase.program 6) (place i)

def resetProgram (i : Fin 7) : Program 7 2 1 :=
  reindex (extend (PartitionPass.reset 0) 3) (place i)

private def single (v : Tapes 7 1) (i : Fin 7) : Tapes 1 1 :=
  ⟨fun _ => v.head i, fun _ => v.tape i⟩

private def six (v : Tapes 7 1) (i : Fin 7) : Tapes 6 1 :=
  ⟨fun j => v.head (place i (Fin.natAdd 1 j)), fun j => v.tape (place i (Fin.natAdd 1 j))⟩

private theorem single_view (v : Tapes 7 1) (i : Fin 7) :
    ((single v i).append (six v i)).reindex (place i) = v := by
  cases v with | mk heads tapes =>
    unfold single six Tapes.append Tapes.reindex
    congr 1
    · funext j; fin_cases i <;> fin_cases j <;> rfl
    · funext j; fin_cases i <;> fin_cases j <;> rfl

private theorem erase_exact (v : Tapes 7 1) (i : Fin 7) (word : List (Fin 4))
    (htape : v.tape i = markedTape 0 word) (hhead : v.head i = word.length) :
    ExactRun (eraseProgram i) (word.length + 2) v (clean v i) := by
  have hnon : ∀ x ∈ word.map encoding.encode, x ≠ marker := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact encoding_ne_marker y
  obtain ⟨hr, hh⟩ := Erase.erase_exact 0 (word.map encoding.encode) hnon
  simp only [List.length_map, zero_add, ← markedTape_putWord] at hr hh
  have hrun := reindex_run (extend Erase.program 6) (place i) (extend_run Erase.program (six v i) hr)
  have hhalt := reindex_halt (extend Erase.program 6) (place i) (extend_halt Erase.program (six v i) hh)
  have hbefore : ((Erase.cfg (markedTape 0 word) word.length 0).extend (six v i)).reindex (place i) =
      v.start (eraseProgram i) := by
    have ht := single_view v i
    unfold single at ht
    rw [htape, hhead] at ht
    unfold Config.reindex Config.extend Tapes.start Erase.cfg
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  change ((⟨fun _ => 0, fun _ => markedTape 0 []⟩ : Tapes 1 1).append (six v i)).reindex (place i) = clean v i
  unfold clean Tapes.append Tapes.reindex six
  congr 1
  · funext j; fin_cases i <;> fin_cases j <;> rfl
  · funext j; fin_cases i <;> fin_cases j <;> rfl

private def four (v : Tapes 7 1) (i : Fin 7) : Tapes 4 1 :=
  ⟨fun j => v.head (place i (Fin.castAdd 3 j)), fun j => v.tape (place i (Fin.castAdd 3 j))⟩

private def three (v : Tapes 7 1) (i : Fin 7) : Tapes 3 1 :=
  ⟨fun j => v.head (place i (Fin.natAdd 4 j)), fun j => v.tape (place i (Fin.natAdd 4 j))⟩

private theorem four_view (v : Tapes 7 1) (i : Fin 7) :
    ((four v i).append (three v i)).reindex (place i) = v := by
  cases v with | mk heads tapes =>
    unfold four three Tapes.append Tapes.reindex
    congr 1
    · funext j; fin_cases i <;> fin_cases j <;> rfl
    · funext j; fin_cases i <;> fin_cases j <;> rfl

private theorem reset_exact (v : Tapes 7 1) (i : Fin 7) (word : List (Fin 4)) (distance : ℕ)
    (htape : v.tape i = markedTape 0 word) (hhead : v.head i = distance) :
    ExactRun (resetProgram i) (distance + 2) v (positioned v i) := by
  have htape' : (four v i).tape 0 = markedTape 0 word := by
    simpa [four, place] using htape
  have hhead' : (four v i).head 0 = 0 + (distance : ℤ) := by
    simpa [four, place] using hhead
  obtain ⟨hr, hh⟩ := PartitionPass.reset_exact (four v i) 0 0 word distance htape' hhead'
  have hrun := reindex_run (extend (PartitionPass.reset 0) 3) (place i)
    (extend_run (PartitionPass.reset 0) (three v i) hr)
  have hhalt := reindex_halt (extend (PartitionPass.reset 0) 3) (place i)
    (extend_halt (PartitionPass.reset 0) (three v i) hh)
  have hbefore : (((four v i).start (PartitionPass.reset 0)).extend (three v i)).reindex (place i) =
      v.start (resetProgram i) := by
    have ht := four_view v i
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  change (Tapes.append ⟨Function.update (four v i).head 0 0, (four v i).tape⟩
    (three v i)).reindex (place i) = positioned v i
  unfold four three Tapes.append Tapes.reindex positioned
  congr 1
  · funext j; fin_cases i <;> fin_cases j <;> rfl
  · funext j; fin_cases i <;> fin_cases j <;> rfl

private theorem clean_source (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    clean (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 0 =
      KeyPass.bank k [] flags zeros ones sf output 0 hF hZ hO hS hOut := by
  unfold clean KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem clean_flags (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    clean (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 2 =
      KeyPass.bank k records [] zeros ones sf output h₀ 0 hZ hO hS hOut := by
  unfold clean KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem clean_zeros (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    clean (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 3 =
      KeyPass.bank k records flags [] ones sf output h₀ hF 0 hO hS hOut := by
  unfold clean KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem clean_ones (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    clean (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 4 =
      KeyPass.bank k records flags zeros [] sf output h₀ hF hZ 0 hS hOut := by
  unfold clean KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem position_source (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    positioned (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 0 =
      KeyPass.bank k records flags zeros ones sf output 0 hF hZ hO hS hOut := by
  unfold positioned KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  funext i; fin_cases i <;> rfl

private theorem position_output (k : ℕ) (records output : List (List Bool))
    (flags zeros ones sf : List (Fin 4)) (h₀ hF hZ hO hS hOut : ℤ) :
    positioned (KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS hOut) 6 =
      KeyPass.bank k records flags zeros ones sf output h₀ hF hZ hO hS 0 := by
  unfold positioned KeyPass.bank KeyPartition.bank Tapes.append
  congr 1
  funext i; fin_cases i <;> rfl

/-- Move the separate new raw output back to the cleared original input tape.
The permutation only selects the copy subroutine's physical tape slots. -/
def movePlacement : Fin 7 ≃ Fin 7 where
  toFun := fun i => if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 1
    else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3
    else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else 0
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def moveProgram : Program 7 1 1 := reindex (extend (Copy.program blank true) 5) movePlacement

private def moveExtra (k : ℕ) : Tapes 5 1 :=
  ⟨fun _ => 0, fun i => if i = 0 then KeySelect.selector k else markedTape 0 []⟩

private theorem move_bank (k : ℕ) (source dest : List (List Bool)) (hs hd : ℤ) :
    ((Copy.tapes (KeyPartition.rawTape source) (KeyPartition.rawTape dest) hs hd).append
      (moveExtra k)).reindex movePlacement = KeyPass.bank k dest [] [] [] [] source hd 0 0 0 0 hs := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex moveExtra
    KeyPass.bank KeyPartition.bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem raw_nonblank (records : List (List Bool)) :
    ∀ x ∈ KeySelect.encode records, x ≠ blank := by
  induction records with
  | nil => simp [KeySelect.encode]
  | cons bits rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact KeySelect.recordWord_nonblank bits x h
    · exact ih x h

private theorem empty_after (n : ℕ) : markedTape 0 [] n = blank := by
  have hn : (n : ℤ) ≠ 0 - 1 := by omega
  simp only [markedTape, hn, ↓reduceIte, putWord]
  rfl

private theorem move_exact (k : ℕ) (records : List (List Bool)) :
    ExactRun moveProgram (KeySelect.encode records).length
      (KeyPass.bank k [] [] [] [] [] records 0 0 0 0 0 0)
      (KeyPass.bank k records [] [] [] [] [] (KeySelect.encode records).length 0 0 0 0
        (KeySelect.encode records).length) := by
  obtain ⟨hr, hh⟩ := Copy.copy_exact blank true (markedTape 0 []) (markedTape 0 [])
    0 0 (KeySelect.encode records) (raw_nonblank records)
    (by simpa only [zero_add] using empty_after (KeySelect.encode records).length)
  have herased : putWord (markedTape 0 []) 0 ((KeySelect.encode records).map (Copy.retained true)) =
      markedTape 0 [] := DropFlag.erase_marked_word 0 _
  simp only [herased, zero_add] at hr hh
  have hrun := reindex_run (extend (Copy.program blank true) 5) movePlacement
    (extend_run (Copy.program blank true) (moveExtra k) hr)
  have hhalt := reindex_halt (extend (Copy.program blank true) 5) movePlacement
    (extend_halt (Copy.program blank true) (moveExtra k) hh)
  have hbefore : ((Copy.cfg (KeyPartition.rawTape records) (KeyPartition.rawTape []) 0 0).extend
      (moveExtra k)).reindex movePlacement =
      (KeyPass.bank k [] [] [] [] [] records 0 0 0 0 0 0).start moveProgram := by
    have ht := move_bank k records [] 0 0
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  change run moveProgram (KeySelect.encode records).length
    (((Copy.cfg (KeyPartition.rawTape records) (KeyPartition.rawTape []) 0 0).extend
      (moveExtra k)).reindex movePlacement) = _ at hrun
  rw [hbefore] at hrun
  exact ⟨_, hrun, hhalt, move_bank k [] records (KeySelect.encode records).length
    (KeySelect.encode records).length⟩

/-- Cleanup is itself a fixed finite program: clear four obsolete streams,
rewind the new raw output, physically move it back, then reset both copy heads. -/
def cleanupProgram : Program 7 15 1 :=
  seq (seq (seq (seq (seq (seq (seq (eraseProgram 0) (eraseProgram 2)) (eraseProgram 3))
    (eraseProgram 4)) (resetProgram 6)) moveProgram) (resetProgram 0)) (resetProgram 6)

def cleanupTime (k : ℕ) (records : List (List Bool)) : ℕ :=
  5 * (KeySelect.encode records).length + 2 * (KeyPartition.flagWord k records).length + 21

private theorem cleanup_exact (k : ℕ) (records : List (List Bool)) :
    ExactRun cleanupProgram (cleanupTime k records)
      (KeyPass.bank k records (KeyPartition.flagWord k records)
        (Partition.bucket false (KeyPartition.selected k records))
        (Partition.bucket true (KeyPartition.selected k records)) [] (KeyPass.sorted k records)
        (KeySelect.encode records).length (KeyPartition.flagWord k records).length
        (Partition.bucket false (KeyPartition.selected k records)).length
        (Partition.bucket true (KeyPartition.selected k records)).length 0 (KeySelect.encode records).length)
      (KeyPass.bank k (KeyPass.sorted k records) [] [] [] [] [] 0 0 0 0 0 0) := by
  let n := (KeySelect.encode records).length
  let flags := KeyPartition.flagWord k records
  let low := Partition.bucket false (KeyPartition.selected k records)
  let high := Partition.bucket true (KeyPartition.selected k records)
  let result := KeyPass.sorted k records
  let v₀ := KeyPass.bank k records flags low high [] result n flags.length low.length high.length 0 n
  let v₁ := KeyPass.bank k [] flags low high [] result 0 flags.length low.length high.length 0 n
  let v₂ := KeyPass.bank k [] [] low high [] result 0 0 low.length high.length 0 n
  let v₃ := KeyPass.bank k [] [] [] high [] result 0 0 0 high.length 0 n
  let v₄ := KeyPass.bank k [] [] [] [] [] result 0 0 0 0 0 n
  let v₅ := KeyPass.bank k [] [] [] [] [] result 0 0 0 0 0 0
  let v₆ := KeyPass.bank k result [] [] [] [] [] n 0 0 0 0 n
  let v₇ := KeyPass.bank k result [] [] [] [] [] 0 0 0 0 0 n
  let v₈ := KeyPass.bank k result [] [] [] [] [] 0 0 0 0 0 0
  have h₀ : ExactRun (eraseProgram 0) (n + 2) v₀ v₁ := by
    have h := erase_exact v₀ 0 (rawWord records) (rawTape_marked records)
      (by change (n : ℤ) = (rawWord records).length; rw [rawWord_length])
    simpa only [v₀, v₁, clean_source, rawWord_length, n] using h
  have h₁ : ExactRun (eraseProgram 2) (flags.length + 2) v₁ v₂ := by
    simpa only [v₁, v₂, clean_flags] using erase_exact v₁ 2 flags rfl rfl
  have h₂ : ExactRun (eraseProgram 3) (low.length + 2) v₂ v₃ := by
    simpa only [v₂, v₃, clean_zeros] using erase_exact v₂ 3 low rfl rfl
  have h₃ : ExactRun (eraseProgram 4) (high.length + 2) v₃ v₄ := by
    simpa only [v₃, v₄, clean_ones] using erase_exact v₃ 4 high rfl rfl
  have h₄ : ExactRun (resetProgram 6) (n + 2) v₄ v₅ := by
    simpa only [v₄, v₅, position_output] using
      reset_exact v₄ 6 (rawWord result) n (rawTape_marked result) rfl
  have h₅ : ExactRun moveProgram n v₅ v₆ := by
    simpa only [result, v₅, v₆, n, KeyPass.sorted_raw_length] using move_exact k result
  have h₆ : ExactRun (resetProgram 0) (n + 2) v₆ v₇ := by
    simpa only [v₆, v₇, position_source] using
      reset_exact v₆ 0 (rawWord result) n (rawTape_marked result) rfl
  have h₇ : ExactRun (resetProgram 6) (n + 2) v₇ v₈ := by
    simpa only [v₇, v₈, position_output] using reset_exact v₇ 6 [] n rfl rfl
  have ht := exact_seq (exact_seq (exact_seq (exact_seq (exact_seq (exact_seq (exact_seq
    h₀ h₁) h₂) h₃) h₄) h₅) h₆) h₇
  have hvol : low.length + high.length = flags.length :=
    Partition.bucket_lengths (KeyPartition.selected k records)
  have hcost : n + 2 + 1 + (flags.length + 2) + 1 + (low.length + 2) + 1 + (high.length + 2) +
      1 + (n + 2) + 1 + n + 1 + (n + 2) + 1 + (n + 2) = cleanupTime k records := by
    unfold cleanupTime
    change _ = 5 * n + 2 * flags.length + 21
    omega
  simpa only [hcost, cleanupProgram, v₀, v₈, n, flags, low, high, result] using ht

/-- A complete reusable stable raw-record pass with literal destructive cleanup. -/
def program : Program 7 36 1 := seq KeyPass.program cleanupProgram

def runtime (k : ℕ) (records : List (List Bool)) : ℕ :=
  KeyPass.runtime k records + 5 * (KeySelect.encode records).length +
    2 * (KeyPartition.flagWord k records).length + 22

/-- The exact fresh input bank is restored on the same physical tape slots.
Only the record order changes; every work tape is empty and every head is zero. -/
theorem pass_exact (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ∃ c, run program (runtime k records)
      ((KeyPass.bank k records [] [] [] [] [] 0 0 0 0 0 0).start program) = some c ∧
      step program c = none ∧
      c.tapes = KeyPass.bank k (KeyPass.sorted k records) [] [] [] [] [] 0 0 0 0 0 0 := by
  have hp : ExactRun KeyPass.program (KeyPass.runtime k records)
      (KeyPass.bank k records [] [] [] [] [] 0 0 0 0 0 0)
      (KeyPass.bank k records (KeyPartition.flagWord k records)
        (Partition.bucket false (KeyPartition.selected k records))
        (Partition.bucket true (KeyPartition.selected k records)) [] (KeyPass.sorted k records)
        (KeySelect.encode records).length (KeyPartition.flagWord k records).length
        (Partition.bucket false (KeyPartition.selected k records)).length
        (Partition.bucket true (KeyPartition.selected k records)).length 0 (KeySelect.encode records).length) :=
    KeyPass.pass_exact k records hvalid
  have ht := exact_seq hp (cleanup_exact k records)
  have hcost : KeyPass.runtime k records + 1 + cleanupTime k records = runtime k records := by
    unfold cleanupTime runtime
    omega
  simpa only [hcost, program, ExactRun] using ht

theorem pass_hoare (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    HoareTime program
      (fun v => v = KeyPass.bank k records [] [] [] [] [] 0 0 0 0 0 0)
      (fun v => v = KeyPass.bank k (KeyPass.sorted k records) [] [] [] [] [] 0 0 0 0 0 0)
      (runtime k records) := by
  rintro v rfl
  obtain ⟨c, hr, hh, hc⟩ := pass_exact k records hvalid
  exact ⟨_, c, le_rfl, hr, hh, hc⟩

/-- Constant-factor linear time includes physical move-back and every reset. -/
theorem runtime_le_linear (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    runtime k records ≤ 26 * (KeySelect.encode records).length + 41 := by
  have hp := KeyPass.runtime_le_linear k records hvalid
  have hi := KeySelect.index_volume k records hvalid
  have hr : records.length ≤ (KeySelect.encode records).length := by nlinarith
  unfold runtime
  rw [KeyPartition.flagWord_length]
  omega

end IntegerMultBounds.Machine.KeyPassReuse
