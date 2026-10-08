import IntegerMultBounds.Machine.KeyPassReuse
import IntegerMultBounds.Machine.UnarySelector
import IntegerMultBounds.Machine.Loop

/-! A fixed eight-tape terminating radix-sort controller. A unary width tape
supplies the number of passes; its advancing head denotes the remaining suffix.
The reusable stable pass handles physical selection, routing, flag deletion,
move-back, and cleanup. Empty record streams halt without scanning the width. -/

namespace IntegerMultBounds.Machine.TapeRadixSort

open PartitionMarked

/-- Record key bits, stored least significant position first. -/
def bit (record : List Bool) (index : ℕ) : Bool := KeySelect.keyAt index record

/-- Seven reusable data/selector tapes plus a preserved unary width tape whose
head marks the next remaining pass. All other heads are at their origins. -/
def bank (width index : ℕ) (records : List (List Bool)) : Tapes 8 1 :=
  (KeyPass.bank index records [] [] [] [] [] 0 0 0 0 0 0).append
    (⟨fun _ => index, fun _ => KeySelect.selector width⟩ : Tapes 1 1)

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

/-- Unary increment uses the selector in slot one and the width cursor in seven. -/
def incrementPlacement : Fin 8 ≃ Fin 8 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 7 else if i = 2 then 0
    else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else 6
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3
    else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else 1
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def incrementProgram : Program 8 3 1 :=
  reindex (extend UnarySelector.program 6) incrementPlacement

private def incrementExtra (records : List (List Bool)) : Tapes 6 1 :=
  ⟨fun _ => 0, fun i => if i = 0 then KeyPartition.rawTape records else markedTape 0 []⟩

private theorem increment_bank (width k : ℕ) (records : List (List Bool)) :
    ((UnarySelector.cfg (KeySelect.selector k) (KeySelect.selector width) 0 k 0).tapes.append
      (incrementExtra records)).reindex incrementPlacement = bank width k records := by
  unfold UnarySelector.cfg Config.tapes Tapes.append Tapes.reindex incrementExtra bank
    KeyPass.bank KeyPartition.bank
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem increment_exact (width k : ℕ) (records : List (List Bool)) :
    ExactRun incrementProgram (2 * k + 2) (bank width k records) (bank width (k + 1) records) := by
  obtain ⟨hr, hh⟩ := UnarySelector.increment_exact k (KeySelect.selector width) k
  have hrun := reindex_run (extend UnarySelector.program 6) incrementPlacement
    (extend_run UnarySelector.program (incrementExtra records) hr)
  have hhalt := reindex_halt (extend UnarySelector.program 6) incrementPlacement
    (extend_halt UnarySelector.program (incrementExtra records) hh)
  have hbefore :
      ((UnarySelector.cfg (KeySelect.selector k) (KeySelect.selector width) 0 k 0).extend
        (incrementExtra records)).reindex incrementPlacement = (bank width k records).start incrementProgram := by
    have ht := increment_bank width k records
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  have ht := increment_bank width (k + 1) records
  change ((UnarySelector.cfg (KeySelect.selector (k + 1)) (KeySelect.selector width) 0 ((k : ℤ) + 1) 0).tapes.append
    (incrementExtra records)).reindex incrementPlacement = _
  simpa only [Nat.cast_add, Nat.cast_one] using ht

private theorem pass_exact (width k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ExactRun (extend KeyPassReuse.program 1) (KeyPassReuse.runtime k records)
      (bank width k records) (bank width k (KeyPass.sorted k records)) := by
  obtain ⟨c, hr, hh, hc⟩ := KeyPassReuse.pass_exact k records hvalid
  let extra : Tapes 1 1 := ⟨fun _ => k, fun _ => KeySelect.selector width⟩
  refine ⟨c.extend extra, extend_run KeyPassReuse.program extra hr,
    extend_halt KeyPassReuse.program extra hh, ?_⟩
  change c.tapes.append extra = _
  rw [hc]
  rfl

/-- One body performs a complete stable pass and advances both unary cursors. -/
def body : Program 8 39 1 := seq (extend KeyPassReuse.program 1) incrementProgram

private theorem body_exact (width k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    ExactRun body (KeyPassReuse.runtime k records + 2 * k + 3)
      (bank width k records) (bank width (k + 1) (KeyPass.sorted k records)) := by
  have h := exact_seq (pass_exact width k records hvalid)
    (increment_exact width k (KeyPass.sorted k records))
  have ht : KeyPassReuse.runtime k records + 1 + (2 * k + 2) =
      KeyPassReuse.runtime k records + 2 * k + 3 := by omega
  simpa only [ht, body] using h

/-- Both tests inspect only the currently scanned symbols. Empty source streams
stop immediately; otherwise each nonblank width symbol authorizes one pass. -/
def test (symbols : Fin 8 → Fin 5) : Bool :=
  decide (symbols 0 ≠ blank) && decide (symbols 7 ≠ blank)

def program : Program 8 40 1 := whileLoop body test

private theorem raw_nonempty (records : List (List Bool)) (h : records ≠ []) :
    KeyPartition.rawTape records 0 ≠ blank := by
  cases records with
  | nil => contradiction
  | cons bits rest =>
    cases bits with
    | nil =>
      change putWord (markedTape 0 []) 0 (separator :: KeySelect.encode rest) 0 ≠ blank
      rw [putWord_head]
      decide
    | cons b bits =>
      change putWord (markedTape 0 []) 0
        (bitSymbol b :: ((bits.map bitSymbol ++ [separator]) ++ KeySelect.encode rest)) 0 ≠ blank
      rw [putWord_head]
      cases b <;> decide

private theorem test_true (width k : ℕ) (records : List (List Bool))
    (hnonempty : records ≠ []) (hk : k < width) : test (bank width k records).reads = true := by
  change (decide (KeyPartition.rawTape records 0 ≠ blank) &&
    decide (KeySelect.selector width k ≠ blank)) = true
  rw [KeySelect.selector_inside width k hk]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact decide_eq_true (raw_nonempty records hnonempty)
  · decide

private theorem test_empty (width k : ℕ) : test (bank width k []).reads = false := by rfl

private theorem test_done (width : ℕ) (records : List (List Bool)) :
    test (bank width width records).reads = false := by
  change (decide (KeyPartition.rawTape records 0 ≠ blank) &&
    decide (KeySelect.selector width width ≠ blank)) = false
  rw [KeySelect.selector_end]
  simp

/-- The exact pass cost plus the selector increment, sequence join, and the
loop's enter/return transitions. -/
def iterationTime (k : ℕ) (records : List (List Bool)) : ℕ :=
  KeyPassReuse.runtime k records + 2 * k + 5

private theorem iteration_exact (width k : ℕ) (records : List (List Bool))
    (hne : records ≠ []) (hk : k < width) (hvalid : ∀ bits ∈ records, k < bits.length) :
    run program (iterationTime k records) ((bank width k records).start program) =
      some ((bank width (k + 1) (KeyPass.sorted k records)).start program) := by
  obtain ⟨c, hr, hh, hc⟩ := body_exact width k records hvalid
  have ht := while_run_iteration body test (bank width k records) (test_true width k records hne hk) hr hh
  rw [hc] at ht
  have htime : KeyPassReuse.runtime k records + 2 * k + 3 + 2 = iterationTime k records := by
    unfold iterationTime
    omega
  simpa only [htime, program] using ht

/-- Exact sum of the actual successive iteration costs. This is a specification
of the concrete execution already proved for `body`, not an assumed runtime. -/
def costFrom (original : List (List Bool)) (index : ℕ) : ℕ → ℕ
  | 0 => 0
  | remaining + 1 =>
      iterationTime index (RadixSort.sort bit index original) +
        costFrom original (index + 1) remaining

private theorem sorted_nonempty (k : ℕ) (records : List (List Bool)) (h : records ≠ []) :
    RadixSort.sort bit k records ≠ [] := by
  intro he
  have hl := RadixSort.sort_length bit k records
  rw [he] at hl
  have hr : records.length = 0 := by simpa using hl.symm
  exact h (List.length_eq_zero_iff.mp hr)

private theorem sorted_valid (width k : ℕ) (records : List (List Bool))
    (h : ∀ bits ∈ records, width ≤ bits.length) (hk : k < width) :
    ∀ bits ∈ RadixSort.sort bit k records, k < bits.length := by
  intro bits hb
  have hmem := (RadixSort.sort_perm bit k records).mem_iff.mp hb
  have hv := h bits hmem
  omega

private theorem run_from (width remaining : ℕ) (original : List (List Bool))
    (hne : original ≠ []) (hvalid : ∀ bits ∈ original, width ≤ bits.length) :
    ∀ k, k + remaining = width →
      run program (costFrom original k remaining)
        ((bank width k (RadixSort.sort bit k original)).start program) =
        some ((bank width width (RadixSort.sort bit width original)).start program) := by
  induction remaining with
  | zero =>
    intro k hk
    have hkw : k = width := by omega
    subst k
    rfl
  | succ remaining ih =>
    intro k hk
    have hstep := iteration_exact width k (RadixSort.sort bit k original)
      (sorted_nonempty k original hne) (by omega) (sorted_valid width k original hvalid (by omega))
    change run program (iterationTime k (RadixSort.sort bit k original))
      ((bank width k (RadixSort.sort bit k original)).start program) =
      some ((bank width (k + 1) (RadixSort.sort bit (k + 1) original)).start program) at hstep
    rw [costFrom, run_add, hstep]
    simp only [Option.bind_some]
    exact ih (k + 1) (by omega)

private theorem sort_nil (width : ℕ) : RadixSort.sort bit width [] = [] := by
  induction width with
  | zero => rfl
  | succ width ih => simp [RadixSort.sort, RadixSort.pass, ih]

/-- Empty streams bypass every pass; otherwise the selector/cursor end at width. -/
def completed (width : ℕ) (records : List (List Bool)) : ℕ := if records = [] then 0 else width

def runtime (width : ℕ) (records : List (List Bool)) : ℕ :=
  if records = [] then 0 else costFrom records 0 width

/-- Full raw radix sort in one fixed finite machine, with exact runtime and a
whole-bank output. Work buffers are empty, input holds the sorted records, and
only the width cursor and unary selector record how many passes completed. -/
theorem sort_exact (width : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    run program (runtime width records) ((bank width 0 records).start program) =
      some ((bank width (completed width records) (RadixSort.sort bit width records)).start program) ∧
    step program ((bank width (completed width records)
      (RadixSort.sort bit width records)).start program) = none := by
  by_cases hne : records = []
  · subst records
    simp only [runtime, completed, ↓reduceIte, sort_nil]
    exact ⟨rfl, while_step_exit body test (bank width 0 []) (test_empty width 0)⟩
  · simp only [runtime, completed, hne, ↓reduceIte]
    exact ⟨run_from width width records hne hvalid 0 (by omega),
      while_step_exit body test _ (test_done width _)⟩

theorem sort_hoare (width : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    HoareTime program (fun v => v = bank width 0 records)
      (fun v => v = bank width (completed width records) (RadixSort.sort bit width records))
      (runtime width records) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := sort_exact width records hvalid
  exact ⟨_, _, le_rfl, hr, hh, rfl⟩

/-- Variable payload lengths are preserved by every stable sorting pass. -/
theorem volume_sort (k : ℕ) (records : List (List Bool)) :
    (KeySelect.encode (RadixSort.sort bit k records)).length = (KeySelect.encode records).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (KeySelect.encode (KeyPass.sorted k (RadixSort.sort bit k records))).length = _
    rw [KeyPass.sorted_raw_length, ih]

private theorem costFrom_le (width remaining : ℕ) (original : List (List Bool))
    (hvalid : ∀ bits ∈ original, width ≤ bits.length) :
    ∀ k, k + remaining ≤ width →
      costFrom original k remaining ≤
        remaining * (26 * (KeySelect.encode original).length + 2 * width + 46) := by
  induction remaining with
  | zero => intro k hk; simp [costFrom]
  | succ remaining ih =>
    intro k hk
    have hc := KeyPassReuse.runtime_le_linear k (RadixSort.sort bit k original)
      (sorted_valid width k original hvalid (by omega))
    rw [volume_sort] at hc
    have hiter : iterationTime k (RadixSort.sort bit k original) ≤
        26 * (KeySelect.encode original).length + 2 * width + 46 := by
      unfold iterationTime
      omega
    have htail := ih (k + 1) (by omega)
    rw [costFrom]
    calc
      _ ≤ (26 * (KeySelect.encode original).length + 2 * width + 46) +
          remaining * (26 * (KeySelect.encode original).length + 2 * width + 46) :=
        Nat.add_le_add hiter htail
      _ = (remaining + 1) * (26 * (KeySelect.encode original).length + 2 * width + 46) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-- An explicit bound even before charging selector scans to record volume. -/
theorem runtime_le_with_width (width : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    runtime width records ≤ width * (26 * (KeySelect.encode records).length + 2 * width + 46) := by
  by_cases h : records = []
  · simp [runtime, h]
  · simpa only [runtime, h, ↓reduceIte] using costFrom_le width width records hvalid 0 (by omega)

private theorem width_volume (width : ℕ) (records : List (List Bool))
    (hne : records ≠ []) (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    width ≤ (KeySelect.encode records).length ∧ 1 ≤ (KeySelect.encode records).length := by
  cases records with
  | nil => contradiction
  | cons bits rest =>
    have h := hvalid bits (by simp)
    simp only [KeySelect.encode, KeySelect.recordWord, List.length_append, List.length_map,
      List.length_singleton]
    omega

/-- Full sorting costs width times encoded stream volume with a uniform
constant. Empty streams cost zero, independently of the supplied unary width. -/
theorem runtime_le_volume (width : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    runtime width records ≤ 74 * width * (KeySelect.encode records).length := by
  by_cases h : records = []
  · simp [runtime, h]
  · obtain ⟨hw, hn⟩ := width_volume width records h hvalid
    have hinner : 26 * (KeySelect.encode records).length + 2 * width + 46 ≤
        74 * (KeySelect.encode records).length := by omega
    calc
      _ ≤ width * (26 * (KeySelect.encode records).length + 2 * width + 46) :=
        runtime_le_with_width width records hvalid
      _ ≤ width * (74 * (KeySelect.encode records).length) := Nat.mul_le_mul_left width hinner
      _ = _ := by ring

theorem sort_hoare_volume (width : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, width ≤ bits.length) :
    HoareTime program (fun v => v = bank width 0 records)
      (fun v => v = bank width (completed width records) (RadixSort.sort bit width records))
      (74 * width * (KeySelect.encode records).length) :=
  (sort_hoare width records hvalid).consequence (fun _ h => h) (fun _ h => h)
    (runtime_le_volume width records hvalid)

end IntegerMultBounds.Machine.TapeRadixSort
