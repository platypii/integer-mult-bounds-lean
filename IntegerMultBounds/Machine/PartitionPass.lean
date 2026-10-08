import IntegerMultBounds.Machine.PartitionMarked
import IntegerMultBounds.Machine.Concatenate
import IntegerMultBounds.Machine.Frame
import IntegerMultBounds.Machine.PartitionSort

/-! A complete literal stable partition pass on four tapes. The input and two
bucket tapes have distinct left markers; the fourth is the output. Bucket heads
are rewound before concatenation. Every phase connection and head movement is
included in the time bound. This is one leading-key-bit pass, not full sorting. -/

namespace IntegerMultBounds.Machine.PartitionPass

open PartitionMarked

private def setHead (v : Tapes 4 1) (i : Fin 4) (p : ℤ) : Tapes 4 1 :=
  ⟨Function.update v.head i p, v.tape⟩

private def resetCfg (v : Tapes 4 1) (s : Fin 2) : Config 4 2 1 :=
  ⟨s, v.head, v.tape⟩

/-- Rewind one selected physical tape, then step right off its marker and halt.
Every other tape is read back without moving its head. -/
def reset (i : Fin 4) : Program 4 2 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 1 then none else
    let hit := symbols i = marker
    some (if hit then 1 else 0, fun j =>
      (symbols j, if j = i then if hit then .right else .left else .stay))

private theorem reset_step (v : Tapes 4 1) (i : Fin 4) (p : ℤ)
    (h : v.tape i p ≠ marker) :
    step (reset i) (resetCfg (setHead v i p) 0) =
      some (resetCfg (setHead v i (p - 1)) 0) := by
  simp only [step, reset, resetCfg, setHead, Function.update_self,
    show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, h]
  congr 1
  congr 1
  · funext j
    by_cases hj : j = i <;> simp [hj, Move.offset, sub_eq_add_neg]
  · funext j k
    by_cases hk : k = Function.update v.head i p j
    · rw [hk]; simp
    · simp [hk]

private theorem reset_finish (v : Tapes 4 1) (i : Fin 4) (p : ℤ)
    (h : v.tape i p = marker) :
    step (reset i) (resetCfg (setHead v i p) 0) =
      some (resetCfg (setHead v i (p + 1)) 1) := by
  simp only [step, reset, resetCfg, setHead, Function.update_self,
    show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, h]
  congr 1
  congr 1
  · funext j
    by_cases hj : j = i <;> simp [hj, Move.offset]
  · funext j k
    by_cases hk : k = Function.update v.head i p j
    · rw [hk]; simp
    · simp [hk]

private theorem reset_scan (v : Tapes 4 1) (i : Fin 4) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → v.tape i (p - j) ≠ marker) :
    run (reset i) n (resetCfg (setHead v i p) 0) =
      some (resetCfg (setHead v i (p - n)) 0) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      reset_step v i (p - n) (h n (by omega))

private theorem reset_halt (v : Tapes 4 1) (i : Fin 4) :
    step (reset i) (resetCfg v 1) = none := by simp [step, reset, resetCfg]

/-- Exact reset cost, with all tape cells and the other three heads retained. -/
theorem reset_exact (v : Tapes 4 1) (i : Fin 4) (origin : ℤ)
    (xs : List (Fin 4)) (distance : ℕ)
    (htape : v.tape i = markedTape origin xs) (hhead : v.head i = origin + distance) :
    run (reset i) (distance + 2) (v.start (reset i)) =
      some (resetCfg (setHead v i origin) 1) ∧
    step (reset i) (resetCfg (setHead v i origin) 1) = none := by
  have hv : setHead v i (origin + distance) = v := by
    cases v with | mk heads tapes =>
      simp only [setHead, Tapes.mk.injEq, and_true]
      exact Function.update_eq_self_iff.mpr hhead.symm
  have hr := reset_scan v i (origin + distance) (distance + 1) (by
    intro j hj
    rw [htape]
    apply markedTape_ne_marker
    omega)
  have hpos : origin + (distance : ℤ) - ((distance + 1 : ℕ) : ℤ) = origin - 1 := by omega
  rw [hpos, hv] at hr
  have hf := reset_finish v i (origin - 1) (by rw [htape, markedTape_marker])
  have hback : origin - 1 + 1 = origin := by omega
  rw [hback] at hf
  refine ⟨?_, reset_halt _ i⟩
  change run (reset i) ((distance + 1) + 1) (resetCfg v 0) = _
  rw [run_add, hr]
  simpa only [Option.bind_some, run_one] using hf

/-- Physical tape order is original input, zero bucket, one bucket, final output. -/
def bank (xs ys zs ws : List (Fin 4)) (h₀ h₁ h₂ h₃ : ℤ) : Tapes 4 1 :=
  (PartitionMarked.cfg 0 0 0 xs ys zs h₀ h₁ h₂).tapes.append
    (⟨fun _ => h₃, fun _ => markedTape 0 ws⟩ : Tapes 1 1)

private def ExactRun {t q a : ℕ} (M : Program t q a) (k : ℕ)
    (before after : Tapes t a) : Prop :=
  ∃ c, run M k (before.start M) = some c ∧ step M c = none ∧ c.tapes = after

private theorem exact_seq {t q r a : ℕ} {M : Program t q a} {N : Program t r a}
    {k l : ℕ} {v w z : Tapes t a} (hm : ExactRun M k v w) (hn : ExactRun N l w z) :
    ExactRun (seq M N) (k + 1 + l) v z := by
  obtain ⟨c, hr, hh, hc⟩ := hm
  obtain ⟨d, hs, hd, he⟩ := hn
  refine ⟨d.mapState (Fin.natAdd q), ?_, seq_halt_right M N hd, he⟩
  rw [← hc] at hs
  exact seq_run M N hr hh hs

private theorem partition_exact (records : List Partition.Record) :
    ExactRun (extend PartitionMarked.program 1) (Partition.encode records).length
      (bank (Partition.encode records) [] [] [] 0 0 0 0)
      (bank (Partition.encode records) (Partition.bucket false records)
        (Partition.bucket true records) [] (Partition.encode records).length
        (Partition.bucket false records).length (Partition.bucket true records).length 0) := by
  obtain ⟨hr, hh⟩ := PartitionMarked.stream_exact records 0 0 0
  let extra : Tapes 1 1 := ⟨fun _ => 0, fun _ => markedTape 0 []⟩
  refine ⟨_, extend_run PartitionMarked.program extra hr,
    extend_halt PartitionMarked.program extra hh, ?_⟩
  simp only [zero_add]
  rfl

private theorem reset_one (xs ys zs ws : List (Fin 4)) (h₀ h₂ h₃ : ℤ) :
    ExactRun (reset 1) (ys.length + 2)
      (bank xs ys zs ws h₀ ys.length h₂ h₃) (bank xs ys zs ws h₀ 0 h₂ h₃) := by
  obtain ⟨hr, hh⟩ := reset_exact (bank xs ys zs ws h₀ ys.length h₂ h₃) 1 0 ys ys.length
    rfl (by change (ys.length : ℤ) = 0 + ys.length; omega)
  refine ⟨_, hr, hh, ?_⟩
  unfold resetCfg setHead bank Tapes.append PartitionMarked.cfg Config.tapes
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem reset_two (xs ys zs ws : List (Fin 4)) (h₀ h₁ h₃ : ℤ) :
    ExactRun (reset 2) (zs.length + 2)
      (bank xs ys zs ws h₀ h₁ zs.length h₃) (bank xs ys zs ws h₀ h₁ 0 h₃) := by
  obtain ⟨hr, hh⟩ := reset_exact (bank xs ys zs ws h₀ h₁ zs.length h₃) 2 0 zs zs.length
    rfl (by change (zs.length : ℤ) = 0 + zs.length; omega)
  refine ⟨_, hr, hh, ?_⟩
  unfold resetCfg setHead bank Tapes.append PartitionMarked.cfg Config.tapes
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Relabel the concatenator's three tapes to slots one, two, and three, with
its unchanged fourth tape occupying the original-input slot zero. -/
def concatPlacement : Fin 4 ≃ Fin 4 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
  invFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def concatProgram : Program 4 2 1 :=
  reindex (extend Concatenate.program 1) concatPlacement

private theorem concat_bank (xs ys zs ws : List (Fin 4)) (h₀ h₁ h₂ h₃ : ℤ) :
    ((Concatenate.tapes (markedTape 0 ys) (markedTape 0 zs) (markedTape 0 ws) h₁ h₂ h₃).append
      (⟨fun _ => h₀, fun _ => markedTape 0 xs⟩ : Tapes 1 1)).reindex concatPlacement =
      bank xs ys zs ws h₀ h₁ h₂ h₃ := by
  unfold Tapes.reindex Concatenate.tapes Concatenate.cfg Tapes.append
    Config.tapes bank PartitionMarked.cfg
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

private theorem encoded_nonblank (xs : List (Fin 4)) (h : ∀ x ∈ xs, x ≠ blank) :
    ∀ x ∈ xs.map encoding.encode, x ≠ blank := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  intro he
  apply h y hy
  apply encoding.injective
  exact he

private theorem empty_end (n : ℕ) : markedTape 0 [] n = blank := by
  have hn : (n : ℤ) ≠ 0 - 1 := by omega
  simp only [markedTape, hn, ↓reduceIte, putWord]
  rfl

private theorem concatenate_exact (xs ys zs : List (Fin 4)) (h₀ : ℤ)
    (hy : ∀ x ∈ ys, x ≠ blank) (hz : ∀ x ∈ zs, x ≠ blank) :
    ExactRun concatProgram (ys.length + 1 + zs.length)
      (bank xs ys zs [] h₀ 0 0 0)
      (bank xs ys zs (ys ++ zs) h₀ ys.length zs.length (ys ++ zs).length) := by
  obtain ⟨hr, hh⟩ := Concatenate.concatenate_exact (markedTape 0 []) (markedTape 0 [])
    (markedTape 0 []) 0 0 0 (ys.map encoding.encode) (zs.map encoding.encode)
    (encoded_nonblank ys hy) (encoded_nonblank zs hz)
    (by simpa only [List.length_map, zero_add] using empty_end ys.length)
    (by simpa only [List.length_map, zero_add] using empty_end zs.length)
  simp only [← List.map_append, ← markedTape_putWord, List.length_map, zero_add] at hr hh
  let extra : Tapes 1 1 := ⟨fun _ => h₀, fun _ => markedTape 0 xs⟩
  have hrun := reindex_run (extend (Concatenate.program : Program 3 2 1) 1)
    concatPlacement (extend_run Concatenate.program extra hr)
  have hhalt := reindex_halt (extend (Concatenate.program : Program 3 2 1) 1)
    concatPlacement (extend_halt Concatenate.program extra hh)
  have hbefore :
      ((Concatenate.cfg 0 (markedTape 0 ys) (markedTape 0 zs) (markedTape 0 []) 0 0 0).extend
        extra).reindex concatPlacement = (bank xs ys zs [] h₀ 0 0 0).start concatProgram := by
    have ht := concat_bank xs ys zs [] h₀ 0 0 0
    unfold Config.reindex Config.extend Tapes.start
    congr 1
    · exact congrArg Tapes.head ht
    · exact congrArg Tapes.tape ht
  rw [hbefore] at hrun
  refine ⟨_, hrun, hhalt, ?_⟩
  exact concat_bank xs ys zs (ys ++ zs) h₀ ys.length zs.length (ys ++ zs).length

/-- One fixed finite-state, four-tape leading-bit stable partition pass. -/
def program : Program 4 9 1 :=
  seq (seq (seq (extend PartitionMarked.program 1) (reset 1)) (reset 2)) concatProgram

/-- The complete pass uses three transitions per input symbol plus eight for
sentinel crossings, resets, concatenation switching, and sequential joins. -/
theorem pass_exact (records : List Partition.Record) :
    ∃ c, run program (3 * (Partition.encode records).length + 8)
      ((bank (Partition.encode records) [] [] [] 0 0 0 0).start program) = some c ∧
      step program c = none ∧ c.tapes =
        bank (Partition.encode records) (Partition.bucket false records)
          (Partition.bucket true records)
          (Partition.bucket false records ++ Partition.bucket true records)
          (Partition.encode records).length (Partition.bucket false records).length
          (Partition.bucket true records).length (Partition.encode records).length := by
  have hp := partition_exact records
  have h₁ := reset_one (Partition.encode records) (Partition.bucket false records)
    (Partition.bucket true records) [] (Partition.encode records).length
    (Partition.bucket true records).length 0
  have h₂ := reset_two (Partition.encode records) (Partition.bucket false records)
    (Partition.bucket true records) [] (Partition.encode records).length 0 0
  have hc := concatenate_exact (Partition.encode records) (Partition.bucket false records)
    (Partition.bucket true records) (Partition.encode records).length
    (Partition.bucket_nonblank false records) (Partition.bucket_nonblank true records)
  have h := exact_seq (exact_seq (exact_seq hp h₁) h₂) hc
  have hlen := Partition.bucket_lengths records
  have hcost : ((Partition.encode records).length + 1 +
        ((Partition.bucket false records).length + 2)) + 1 +
        ((Partition.bucket true records).length + 2) + 1 +
        ((Partition.bucket false records).length + 1 + (Partition.bucket true records).length) =
      3 * (Partition.encode records).length + 8 := by omega
  simpa only [hcost, List.length_append, hlen, program, ExactRun] using h

theorem pass_hoare (records : List Partition.Record) :
    HoareTime program
      (fun v => v = bank (Partition.encode records) [] [] [] 0 0 0 0)
      (fun v => v = bank (Partition.encode records) (Partition.bucket false records)
        (Partition.bucket true records)
        (Partition.bucket false records ++ Partition.bucket true records)
        (Partition.encode records).length (Partition.bucket false records).length
        (Partition.bucket true records).length (Partition.encode records).length)
      (3 * (Partition.encode records).length + 8) := by
  rintro v rfl
  obtain ⟨c, hr, hh, hp⟩ := pass_exact records
  exact ⟨_, c, le_rfl, hr, hh, hp⟩

/-- The complete output word is the same stable pass used by the proved list
radix sort. This includes all tape positioning inside this single pass. -/
theorem pass_stable_exact (records : List Partition.Record) :
    ∃ c, run program (3 * (Partition.encode records).length + 8)
      ((bank (Partition.encode records) [] [] [] 0 0 0 0).start program) = some c ∧
      step program c = none ∧ c.tapes =
        bank (Partition.encode records) (Partition.bucket false records)
          (Partition.bucket true records)
          (Partition.encode (RadixSort.pass Partition.Record.key records))
          (Partition.encode records).length (Partition.bucket false records).length
          (Partition.bucket true records).length (Partition.encode records).length := by
  simpa only [Partition.buckets_eq_pass] using pass_exact records

end IntegerMultBounds.Machine.PartitionPass
