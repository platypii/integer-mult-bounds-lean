import IntegerMultBounds.Machine.PartitionMarked

/-! Record encodings for a physically selected key bit. `keyAt` is a data-level
specification; the machine selects that position by scanning a unary tape. -/

namespace IntegerMultBounds.Machine.KeySelect

def keyAt : ℕ → List Bool → Bool
  | _, [] => false
  | 0, b :: _ => b
  | k + 1, _ :: rest => keyAt k rest

theorem keyAt_split (prebits suffix : List Bool) (b : Bool) :
    keyAt prebits.length (prebits ++ b :: suffix) = b := by
  induction prebits with
  | nil => rfl
  | cons x xs ih => simpa only [List.length_cons, List.cons_append, keyAt] using ih

theorem split_key (k : ℕ) (xs : List Bool) (h : k < xs.length) :
    ∃ prebits b suffix, prebits.length = k ∧ xs = prebits ++ b :: suffix := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons b rest => exact ⟨[], b, rest, rfl, rfl⟩
  | succ k ih =>
    cases xs with
    | nil => simp at h
    | cons x rest =>
      obtain ⟨prebits, b, suffix, hp, hr⟩ := ih rest (by simp only [List.length_cons] at h; omega)
      exact ⟨x :: prebits, b, suffix, by simp [hp], by simp [hr]⟩

def recordWord (bits : List Bool) : List (Fin 5) := bits.map bitSymbol ++ [separator]

def encode : List (List Bool) → List (Fin 5)
  | [] => []
  | xs :: rest => recordWord xs ++ encode rest

def flagged (k : ℕ) : List (List Bool) → List (Fin 5)
  | [] => []
  | xs :: rest => (bitSymbol (keyAt k xs) :: recordWord xs) ++ flagged k rest

/-- The flagged stream is exactly the existing partition machine's record
format, retaining the entire original bit list as each record's payload. -/
theorem flagged_partition (k : ℕ) (records : List (List Bool)) :
    flagged k records =
      (Partition.encode (records.map (fun xs => ⟨keyAt k xs, xs⟩))).map
        PartitionMarked.encoding.encode := by
  induction records with
  | nil => rfl
  | cons xs rest ih =>
    simp only [flagged, List.map_cons, Partition.encode, Partition.recordWord,
      List.map_append, List.map_map, ih, recordWord]
    rfl

theorem flagged_length (k : ℕ) (records : List (List Bool)) :
    (flagged k records).length = (encode records).length + records.length := by
  induction records with
  | nil => rfl
  | cons xs rest ih =>
    simp only [flagged, encode, List.length_append, List.length_cons, ih]
    omega

theorem recordWord_nonblank (xs : List Bool) : ∀ x ∈ recordWord xs, x ≠ blank := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  · simp only [List.mem_singleton] at hx
    subst x
    decide

/-- A valid selected position lies inside every record, so resetting its unary
selector never costs more than a constant number of full record scans. -/
theorem index_volume (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    records.length * (k + 1) ≤ (encode records).length := by
  induction records with
  | nil => simp [encode]
  | cons bits rest ih =>
    have hb := hvalid bits (by simp)
    have ht := ih (fun xs hx => hvalid xs (by simp [hx]))
    simp only [encode, recordWord, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem runtime_le_three_volume (k : ℕ) (records : List (List Bool))
    (hvalid : ∀ bits ∈ records, k < bits.length) :
    (encode records).length + records.length * (2 * k + 2) ≤ 3 * (encode records).length := by
  have h := index_volume k records hvalid
  nlinarith

end IntegerMultBounds.Machine.KeySelect
