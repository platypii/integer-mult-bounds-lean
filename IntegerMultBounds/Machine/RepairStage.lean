import IntegerMultBounds.Machine.TapeRadixSort
import IntegerMultBounds.Machine.StripPrefix
import IntegerMultBounds.Machine.ReturnOrigin
import IntegerMultBounds.Machine.Reinsert

/-! The sorting and reinsertion stage of the exceptional-address repair on
literal tapes. Extracted records arrive with their destination-rank keys as a
`k`-bit prefix; one fixed eleven-tape machine radix sorts them by that prefix,
strips the keys, returns the replacement head, and reinserts the records into
the flagged holes of the full stream. The contract is an exact-run Hoare
triple with every tape content and head, and the cost is linear in the key
width times the extracted volume plus the full-stream volume. Computing the
keys and flags from the actual program's output remains a separate stage. -/

namespace IntegerMultBounds.Machine.RepairStage

open Partition (Record)
open PartitionMarked (encoding markedTape)

/-! ### Keyed records and their sorted order -/

/-- A keyed extracted record: key bits, least significant first, then the
flagged record. -/
abbrev Keyed := List Bool × Record

def rawOf (x : Keyed) : List Bool := x.1 ++ x.2.key :: x.2.payload

def keyBit (x : Keyed) (j : ℕ) : Bool := KeySelect.keyAt j x.1

def flaggedBits (r : Record) : List Bool := r.key :: r.payload

theorem keyAt_append_left (xs ys : List Bool) (j : ℕ) (hj : j < xs.length) :
    KeySelect.keyAt j (xs ++ ys) = KeySelect.keyAt j xs := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons b xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simp only [List.length_cons] at hj; omega)

theorem bit_rawOf (x : Keyed) (j : ℕ) (hj : j < x.1.length) :
    TapeRadixSort.bit (rawOf x) j = keyBit x j :=
  keyAt_append_left _ _ j hj

/-- Radix sorting commutes with a record map that preserves the key bits. -/
theorem sort_map {α β : Type*} (g : α → β) (bitα : α → ℕ → Bool) (bitβ : β → ℕ → Bool)
    (k : ℕ) (l : List α) (h : ∀ x ∈ l, ∀ j, j < k → bitβ (g x) j = bitα x j) :
    RadixSort.sort bitβ k (l.map g) = (RadixSort.sort bitα k l).map g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [RadixSort.sort, ih (fun x hx j hj => h x hx j (by omega)), RadixSort.pass,
      List.filter_map, List.map_append]
    have hmem : ∀ x ∈ RadixSort.sort bitα k l, x ∈ l :=
      fun x hx => (RadixSort.sort_perm bitα k l).mem_iff.mp hx
    rw [List.filter_congr (p := (fun y => !bitβ y k) ∘ g) (q := fun x => !bitα x k)
        (l := RadixSort.sort bitα k l) (fun x hx => by
          simp only [Function.comp, h x (hmem x hx) k (Nat.lt_succ_self k)]),
      List.filter_congr (p := (fun y => bitβ y k) ∘ g) (q := fun x => bitα x k)
        (l := RadixSort.sort bitα k l) (fun x hx => by
          simp only [Function.comp, h x (hmem x hx) k (Nat.lt_succ_self k)])]

theorem encode_flagged (rs : List Record) :
    KeySelect.encode (rs.map flaggedBits) = (Partition.encode rs).map encoding.encode := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons, KeySelect.encode, Partition.encode, Partition.recordWord,
      List.map_append, List.map_map, ih, KeySelect.recordWord, flaggedBits]
    rfl

theorem stripped_rawOf (k : ℕ) (l : List Keyed) (hk : ∀ x ∈ l, x.1.length = k) :
    StripPrefix.stripped k (l.map rawOf) = (l.map Prod.snd).map flaggedBits := by
  simp only [StripPrefix.stripped, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  simp only [Function.comp, rawOf, flaggedBits]
  rw [List.drop_left' (hk x hx)]

theorem rawOf_length (x : Keyed) : (rawOf x).length = x.1.length + 1 + x.2.payload.length := by
  simp only [rawOf, List.length_append, List.length_cons]
  omega

theorem putWord_map (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    putWord (fun j => encoding.encode (f j)) p (xs.map encoding.encode) =
      fun j => encoding.encode (putWord f p xs j) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    funext j
    simp only [List.map_cons, putWord, ih]
    by_cases hj : j = p <;> simp [hj]

/-- A blank-backed record stream seen through the alphabet widening. -/
def encTape (xs : List (Fin 4)) : ℤ → Fin 5 :=
  fun j => encoding.encode (putWord (fun _ => blank) 0 xs j)

theorem encTape_eq (xs : List (Fin 4)) :
    putWord (fun _ => blank) 0 (xs.map encoding.encode) = encTape xs :=
  putWord_map (fun _ => blank) 0 xs

theorem encode_nonblank (records : List (List Bool)) :
    ∀ x ∈ KeySelect.encode records, x ≠ blank := by
  induction records with
  | nil => simp [KeySelect.encode]
  | cons bits rest ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact KeySelect.recordWord_nonblank bits x hx
    · exact ih x hx

theorem markedTape_nil (j : ℤ) (hj : 0 ≤ j) : markedTape 0 [] j = blank := by
  simp only [markedTape, putWord]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  rfl

/-! ### Placing fixed routines in the eleven-slot bank -/

theorem hoare_extend_eq {t s q : ℕ} {M : Program t q 1} {X X' : Tapes t 1} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) (extra : Tapes s 1) :
    HoareTime (extend M s) (fun v => v = X.append extra) (fun v => v = X'.append extra) b :=
  (h.extend extra).consequence (fun v hv => ⟨X, rfl, hv⟩)
    (fun v ⟨small, hs, hv⟩ => by rw [hv, hs]) le_rfl

theorem hoare_place {t s u q : ℕ} {M : Program t q 1} {X X' : Tapes t 1} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) (e : Fin (t + s) ≃ Fin u)
    (extra : Tapes s 1) :
    HoareTime (reindex (extend M s) e) (fun v => v = (X.append extra).reindex e)
      (fun v => v = (X'.append extra).reindex e) b :=
  ((hoare_extend_eq h extra).reindex e).consequence (fun v hv => ⟨_, rfl, hv⟩)
    (fun v ⟨orig, ho, hv⟩ => by rw [hv, ho]) le_rfl

theorem hoare_widen {t q : ℕ} {M : Program t q 0} {X X' : Tapes t 0} {b : ℕ}
    (h : HoareTime M (fun v => v = X) (fun v => v = X') b) :
    HoareTime (Alphabet.program encoding M) (fun v => v = Alphabet.mapTapes encoding X)
      (fun v => v = Alphabet.mapTapes encoding X') b :=
  (Alphabet.map_hoare encoding h).consequence (fun v hv => ⟨X, rfl, hv⟩)
    (fun v ⟨orig, ho, hv⟩ => by rw [hv, ho]) le_rfl

/-- Strip tapes: source, width, output at slots 0, 7, 8. -/
def stripPlacement : Fin 11 ≃ Fin 11 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 7 else if i = 2 then 8
    else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else if i = 6 then 4
    else if i = 7 then 5 else if i = 8 then 6 else if i = 9 then 9 else 10
  invFun := fun i => if i = 0 then 0 else if i = 7 then 1 else if i = 8 then 2
    else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 6
    else if i = 5 then 7 else if i = 6 then 8 else if i = 9 then 9 else 10
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- The replacement head return acts on slot 8. -/
def returnPlacement : Fin 11 ≃ Fin 11 where
  toFun := fun i => if i = 0 then 8 else if i = 1 then 0 else if i = 2 then 1
    else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5
    else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 9 else 10
  invFun := fun i => if i = 8 then 0 else if i = 0 then 1 else if i = 1 then 2
    else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6
    else if i = 6 then 7 else if i = 7 then 8 else if i = 9 then 9 else 10
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- Reinsert tapes: originals, replacements, output at slots 9, 8, 10. -/
def reinsertPlacement : Fin 11 ≃ Fin 11 where
  toFun := fun i => if i = 0 then 9 else if i = 1 then 8 else if i = 2 then 10
    else if i = 3 then 0 else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 3
    else if i = 7 then 4 else if i = 8 then 5 else if i = 9 then 6 else 7
  invFun := fun i => if i = 9 then 0 else if i = 8 then 1 else if i = 10 then 2
    else if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 6
    else if i = 4 then 7 else if i = 5 then 8 else if i = 6 then 9 else 10
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def sortPart : Program 11 40 1 := extend TapeRadixSort.program 3
def stripPart : Program 11 4 1 := reindex (extend StripPrefix.program 8) stripPlacement
def returnPart : Program 11 3 1 := reindex (extend ReturnOrigin.program 10) returnPlacement
def reinsertPart : Program 11 4 1 :=
  reindex (extend (Alphabet.program encoding Reinsert.program) 8) reinsertPlacement

/-- Sort, strip, return the replacement head, reinsert. -/
def program : Program 11 (40 + 4 + 3 + 4) 1 :=
  seq (seq (seq sortPart stripPart) returnPart) reinsertPart

/-- The eleven-slot bank: sorted raw stream, pass index, five work tapes, the
unary width, the replacement stream, the flagged full stream, the output. -/
def stage (k idx : ℕ) (raw : List (List Bool)) (h0 h7 : ℤ) (t8 : ℤ → Fin 5) (h8 : ℤ)
    (t9 : ℤ → Fin 5) (h9 : ℤ) (t10 : ℤ → Fin 5) (h10 : ℤ) : Tapes 11 1 where
  head := fun i => if i = 0 then h0 else if i = 7 then h7 else if i = 8 then h8
    else if i = 9 then h9 else if i = 10 then h10 else 0
  tape := fun i => if i = 0 then KeyPartition.rawTape raw
    else if i = 1 then KeySelect.selector idx else if i = 7 then KeySelect.selector k
    else if i = 8 then t8 else if i = 9 then t9 else if i = 10 then t10 else markedTape 0 []

theorem sort_stage (k idx : ℕ) (raw : List (List Bool)) (t8 t9 t10 : ℤ → Fin 5) (h8 h9 h10 : ℤ) :
    (TapeRadixSort.bank k idx raw).append
      (⟨fun i => if i = 0 then h8 else if i = 1 then h9 else h10,
        fun i => if i = 0 then t8 else if i = 1 then t9 else t10⟩ : Tapes 3 1) =
      stage k idx raw 0 idx t8 h8 t9 h9 t10 h10 := by
  unfold TapeRadixSort.bank KeyPass.bank KeyPartition.bank Tapes.append stage
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem strip_stage (k idx : ℕ) (raw : List (List Bool)) (h0 h7 : ℤ) (t8 : ℤ → Fin 5) (h8 : ℤ)
    (t9 : ℤ → Fin 5) (h9 : ℤ) (t10 : ℤ → Fin 5) (h10 : ℤ) (s : Fin 4) :
    ((StripPrefix.cfg (KeyPartition.rawTape raw) (KeySelect.selector k) t8 h0 h7 h8 s).tapes.append
      (⟨fun i => if i = 6 then h9 else if i = 7 then h10 else 0,
        fun i => if i = 0 then KeySelect.selector idx else if i = 6 then t9
          else if i = 7 then t10 else markedTape 0 []⟩ : Tapes 8 1)).reindex stripPlacement =
      stage k idx raw h0 h7 t8 h8 t9 h9 t10 h10 := by
  unfold StripPrefix.cfg Config.tapes Tapes.append Tapes.reindex stage stripPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem return_stage (k idx : ℕ) (raw : List (List Bool)) (h0 h7 : ℤ) (t8 : ℤ → Fin 5) (h8 : ℤ)
    (t9 : ℤ → Fin 5) (h9 : ℤ) (t10 : ℤ → Fin 5) (h10 : ℤ) (s : Fin 3) :
    ((ReturnOrigin.cfg t8 h8 s).tapes.append
      (⟨fun i => if i = 0 then h0 else if i = 7 then h7 else if i = 8 then h9
          else if i = 9 then h10 else 0,
        fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector idx
          else if i = 7 then KeySelect.selector k else if i = 8 then t9
          else if i = 9 then t10 else markedTape 0 []⟩ : Tapes 10 1)).reindex returnPlacement =
      stage k idx raw h0 h7 t8 h8 t9 h9 t10 h10 := by
  unfold ReturnOrigin.cfg Config.tapes Tapes.append Tapes.reindex stage returnPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem reinsert_stage (k idx : ℕ) (raw : List (List Bool)) (h0 h7 : ℤ) (f h g : ℤ → Fin 4)
    (p q r : ℤ) (s : Fin 4) :
    ((Alphabet.mapTapes encoding (Reinsert.cfg false f h g p q r s).tapes).append
      (⟨fun i => if i = 0 then h0 else if i = 7 then h7 else 0,
        fun i => if i = 0 then KeyPartition.rawTape raw else if i = 1 then KeySelect.selector idx
          else if i = 7 then KeySelect.selector k else markedTape 0 []⟩ : Tapes 8 1)).reindex
        reinsertPlacement =
      stage k idx raw h0 h7 (fun j => encoding.encode (h j)) q (fun j => encoding.encode (f j)) p
        (fun j => encoding.encode (g j)) r := by
  unfold Reinsert.cfg Reinsert.source Config.tapes Alphabet.mapTapes Tapes.append Tapes.reindex
    stage reinsertPlacement
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ### The stage contract -/

variable (k : ℕ) (items : List Keyed)

/-- The extracted records as raw sortable words. -/
def raw : List (List Bool) := items.map rawOf

/-- The extracted records in destination order. -/
def sortedItems : List Keyed := RadixSort.sort keyBit k items

def replacements : List Record := (sortedItems k items).map Prod.snd

theorem sorted_raw (hk : ∀ x ∈ items, x.1.length = k) :
    RadixSort.sort TapeRadixSort.bit k (raw items) = (sortedItems k items).map rawOf := by
  rw [raw, sortedItems]
  exact sort_map rawOf keyBit TapeRadixSort.bit k items
    (fun x hx j hj => bit_rawOf x j (by rw [hk x hx]; exact hj))


/-- The sorted raw words. -/
def sortedRaw : List (List Bool) := RadixSort.sort TapeRadixSort.bit k (raw items)

theorem raw_valid (hk : ∀ x ∈ items, x.1.length = k) : ∀ bits ∈ raw items, k ≤ bits.length := by
  intro bits hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  rw [rawOf_length, hk x hx]
  omega

theorem raw_valid_succ (hk : ∀ x ∈ items, x.1.length = k) :
    ∀ bits ∈ raw items, k + 1 ≤ bits.length := by
  intro bits hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  rw [rawOf_length, hk x hx]
  omega

theorem mem_sortedRaw (bits : List Bool) (hb : bits ∈ sortedRaw k items) : bits ∈ raw items :=
  (RadixSort.sort_perm _ _ _).mem_iff.mp hb

theorem sortedRaw_valid (hk : ∀ x ∈ items, x.1.length = k) :
    ∀ bits ∈ sortedRaw k items, k ≤ bits.length :=
  fun bits hb => raw_valid k items hk bits (mem_sortedRaw k items bits hb)

theorem stripped_sorted (hk : ∀ x ∈ items, x.1.length = k) :
    StripPrefix.stripped k (sortedRaw k items) = (replacements k items).map flaggedBits := by
  rw [sortedRaw, sorted_raw k items hk, replacements]
  exact stripped_rawOf k _ (fun x hx => hk x ((RadixSort.sort_perm _ _ _).mem_iff.mp hx))

theorem replacement_tape (hk : ∀ x ∈ items, x.1.length = k) :
    putWord (fun _ => blank) 0 (KeySelect.encode (StripPrefix.stripped k (sortedRaw k items))) =
      encTape (Partition.encode (replacements k items)) := by
  rw [stripped_sorted k items hk, encode_flagged, encTape_eq]

theorem replacement_volume (hk : ∀ x ∈ items, x.1.length = k) :
    (Partition.encode (replacements k items)).length =
      (KeySelect.encode (StripPrefix.stripped k (sortedRaw k items))).length := by
  rw [stripped_sorted k items hk, encode_flagged, List.length_map]

/-- The exact stage contract: from the sort bank holding the keyed extracted
records, the blank replacement slot, the flagged full stream, and a blank
output, the machine halts with the sorted raw words, the stripped replacement
stream, the untouched full stream, and the filled output stream, every head
at the end of its written word except the restored width tape. -/
theorem stage_hoare (hk : ∀ x ∈ items, x.1.length = k) (records : List Record)
    (hc : (replacements k items).length = Reinsert.holes records) :
    HoareTime program
      (fun v => v = stage k 0 (raw items) 0 0 (fun _ => blank) 0
        (encTape (Partition.encode records)) 0 (fun _ => blank) 0)
      (fun v => v = stage k (TapeRadixSort.completed k (raw items)) (sortedRaw k items)
        (KeySelect.encode (sortedRaw k items)).length 0
        (encTape (Partition.encode (replacements k items)))
        (Partition.encode (replacements k items)).length
        (encTape (Partition.encode records)) (Partition.encode records).length
        (encTape (Partition.encode (Reinsert.fill records (replacements k items))))
        (Partition.encode (Reinsert.fill records (replacements k items))).length)
      (74 * k * (KeySelect.encode (raw items)).length + 1 +
        (TapeRadixSort.completed k (raw items) + 2 + ((KeySelect.encode (sortedRaw k items)).length +
          (sortedRaw k items).length * (k + 2))) + 1 +
        ((KeySelect.encode (StripPrefix.stripped k (sortedRaw k items))).length + 2) + 1 +
        ((Partition.encode records).length + (Partition.encode (replacements k items)).length)) := by
  have hsort := hoare_extend_eq (TapeRadixSort.sort_hoare_volume k (raw items) (raw_valid k items hk))
    (⟨fun i => if i = 0 then 0 else if i = 1 then 0 else 0,
      fun i => if i = 0 then (fun _ => blank) else if i = 1 then encTape (Partition.encode records)
        else (fun _ => blank)⟩ : Tapes 3 1)
  rw [sort_stage, sort_stage] at hsort
  have hstrip := hoare_place (StripPrefix.strip_hoare k (sortedRaw k items)
    (sortedRaw_valid k items hk) (markedTape 0 []) (fun _ => blank) 0 0
    (TapeRadixSort.completed k (raw items)) (markedTape_nil _ (by omega))) stripPlacement
    (⟨fun i => if i = 6 then 0 else if i = 7 then 0 else 0,
      fun i => if i = 0 then KeySelect.selector (TapeRadixSort.completed k (raw items))
        else if i = 6 then encTape (Partition.encode records)
        else if i = 7 then (fun _ => blank) else markedTape 0 []⟩ : Tapes 8 1)
  have hraw : putWord (markedTape 0 []) 0 (KeySelect.encode (sortedRaw k items)) =
      KeyPartition.rawTape (sortedRaw k items) := rfl
  rw [hraw, strip_stage, strip_stage] at hstrip
  simp only [zero_add] at hstrip
  have hret := hoare_place (ReturnOrigin.return_hoare
    (KeySelect.encode (StripPrefix.stripped k (sortedRaw k items))) (encode_nonblank _))
    returnPlacement
    (⟨fun i => if i = 0 then ((KeySelect.encode (sortedRaw k items)).length : ℤ)
        else if i = 7 then 0 else if i = 8 then 0 else if i = 9 then 0 else 0,
      fun i => if i = 0 then KeyPartition.rawTape (sortedRaw k items)
        else if i = 1 then KeySelect.selector (TapeRadixSort.completed k (raw items))
        else if i = 7 then KeySelect.selector k
        else if i = 8 then encTape (Partition.encode records)
        else if i = 9 then (fun _ => blank) else markedTape 0 []⟩ : Tapes 10 1)
  rw [return_stage, return_stage] at hret
  have hre := hoare_place (hoare_widen (Reinsert.stream_hoare records (replacements k items)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 hc rfl)) reinsertPlacement
    (⟨fun i => if i = 0 then ((KeySelect.encode (sortedRaw k items)).length : ℤ)
        else if i = 7 then 0 else 0,
      fun i => if i = 0 then KeyPartition.rawTape (sortedRaw k items)
        else if i = 1 then KeySelect.selector (TapeRadixSort.completed k (raw items))
        else if i = 7 then KeySelect.selector k else markedTape 0 []⟩ : Tapes 8 1)
  rw [reinsert_stage, reinsert_stage] at hre
  change HoareTime _
    (fun v => v = stage k (TapeRadixSort.completed k (raw items)) (sortedRaw k items)
      (KeySelect.encode (sortedRaw k items)).length 0
      (encTape (Partition.encode (replacements k items))) 0
      (encTape (Partition.encode records)) 0 (fun _ => blank) 0)
    (fun v => v = stage k (TapeRadixSort.completed k (raw items)) (sortedRaw k items)
      (KeySelect.encode (sortedRaw k items)).length 0
      (encTape (Partition.encode (replacements k items)))
      (0 + (Partition.encode (replacements k items)).length)
      (encTape (Partition.encode records)) (0 + (Partition.encode records).length)
      (encTape (Partition.encode (Reinsert.fill records (replacements k items))))
      (0 + (Partition.encode (Reinsert.fill records (replacements k items))).length)) _ at hre
  simp only [zero_add] at hre
  have hre' := hre.consequence (post' := fun v => v = stage k (TapeRadixSort.completed k (raw items))
      (sortedRaw k items) (KeySelect.encode (sortedRaw k items)).length 0
      (encTape (Partition.encode (replacements k items)))
      (Partition.encode (replacements k items)).length
      (encTape (Partition.encode records)) (Partition.encode records).length
      (encTape (Partition.encode (Reinsert.fill records (replacements k items))))
      (Partition.encode (Reinsert.fill records (replacements k items))).length)
    (pre' := fun v => v = stage k (TapeRadixSort.completed k (raw items)) (sortedRaw k items)
      (KeySelect.encode (sortedRaw k items)).length 0
      (putWord (fun _ => blank) 0 (KeySelect.encode (StripPrefix.stripped k (sortedRaw k items)))) 0
      (encTape (Partition.encode records)) 0 (fun _ => blank) 0)
    (fun v hv => by rw [hv, replacement_tape k items hk]) (fun v hv => hv) le_rfl
  exact ((hsort.seq hstrip).seq hret).seq hre'

theorem encode_length_ge (m : ℕ) (rs : List (List Bool)) (hv : ∀ bits ∈ rs, m ≤ bits.length) :
    rs.length * (m + 1) ≤ (KeySelect.encode rs).length := by
  induction rs with
  | nil => simp [KeySelect.encode]
  | cons bits rest ih =>
    have hb := hv bits (by simp)
    have ih' := ih (fun xs hxs => hv xs (by simp [hxs]))
    simp only [KeySelect.encode, KeySelect.recordWord, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The stage cost is linear: `74k + 4` extracted volumes plus one full-stream
volume plus `k + 7`. -/
theorem stage_cost_le (hk : ∀ x ∈ items, x.1.length = k) (records : List Record) :
    74 * k * (KeySelect.encode (raw items)).length + 1 +
        (TapeRadixSort.completed k (raw items) + 2 + ((KeySelect.encode (sortedRaw k items)).length +
          (sortedRaw k items).length * (k + 2))) + 1 +
        ((KeySelect.encode (StripPrefix.stripped k (sortedRaw k items))).length + 2) + 1 +
        ((Partition.encode records).length + (Partition.encode (replacements k items)).length) ≤
      (74 * k + 4) * (KeySelect.encode (raw items)).length + (Partition.encode records).length +
        k + 7 := by
  have hvol : (KeySelect.encode (sortedRaw k items)).length =
      (KeySelect.encode (raw items)).length := TapeRadixSort.volume_sort k (raw items)
  have hc : TapeRadixSort.completed k (raw items) ≤ k := by
    unfold TapeRadixSort.completed
    split <;> omega
  have hn : (sortedRaw k items).length * (k + 2) ≤ (KeySelect.encode (sortedRaw k items)).length :=
    encode_length_ge (k + 1) _ (fun bits hb =>
      raw_valid_succ k items hk bits (mem_sortedRaw k items bits hb))
  have hs := StripPrefix.stripped_length k (sortedRaw k items) (sortedRaw_valid k items hk)
  have hr := replacement_volume k items hk
  rw [hr]
  nlinarith [hvol, hc, hn, hs]

/-- The extracted volume is at most the record count times the key width,
the flag, the delimiter, and the largest payload. -/
theorem raw_volume_le (hk : ∀ x ∈ items, x.1.length = k) (w : ℕ)
    (hw : ∀ x ∈ items, x.2.payload.length ≤ w) :
    (KeySelect.encode (raw items)).length ≤ items.length * (k + 2 + w) := by
  induction items with
  | nil => simp [raw, KeySelect.encode]
  | cons x rest ih =>
    have hx := hk x (by simp)
    have hwx := hw x (by simp)
    have ih' := ih (fun y hy => hk y (by simp [hy])) (fun y hy => hw y (by simp [hy]))
    simp only [raw, List.map_cons, KeySelect.encode, KeySelect.recordWord, List.length_append,
      List.length_map, rawOf_length, List.length_cons, List.length_nil, Nat.add_mul, Nat.one_mul] at ih' ⊢
    omega

end IntegerMultBounds.Machine.RepairStage
