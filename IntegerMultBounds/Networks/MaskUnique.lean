import IntegerMultBounds.Networks.MaskDAG

/-! Uniqueness certificates use a sorted list of bank positions. Strict masks
force distinct identifiers, and a full-length bounded list covers the bank.
No sorting algorithm or permutation checker is trusted. -/

namespace IntegerMultBounds.Networks.MaskUnique

open MaskDAG
variable {width : ℕ}

abbrev Row (width : ℕ) := ℕ × BitVec width

/-- Check strict increase, bounded IDs and exact static-bank membership. -/
def checkSorted (bank : ℕ → Option (BitVec width)) (bound lower : ℕ) : List (Row width) → Bool
  | [] => true
  | row :: rows =>
    decide (row.1 < bound ∧ bank row.1 = some row.2 ∧ lower < row.2.toNat) &&
      checkSorted bank bound row.2.toNat rows

/-- A chunk's boundary value is independent of its acceptance proof. -/
def lastValue (lower : ℕ) : List (Row width) → ℕ
  | [] => lower
  | row :: rows => lastValue row.2.toNat rows

theorem checkSorted_append (bank : ℕ → Option (BitVec width)) (bound lower : ℕ)
    (first rest : List (Row width)) :
    checkSorted bank bound lower (first ++ rest) =
      (checkSorted bank bound lower first && checkSorted bank bound (lastValue lower first) rest) := by
  induction first generalizing lower with
  | nil => simp [checkSorted, lastValue]
  | cons row first ih => simp [checkSorted, lastValue, ih, Bool.and_assoc]

theorem checkSorted_append_of (bank : ℕ → Option (BitVec width)) (bound lower : ℕ)
    (first rest : List (Row width))
    (hf : checkSorted bank bound lower first = true)
    (hr : checkSorted bank bound (lastValue lower first) rest = true) :
    checkSorted bank bound lower (first ++ rest) = true := by
  rw [checkSorted_append, hf, hr]
  rfl

/-- The checker proves row membership and the complete strict ordering. -/
theorem checkSorted_sound (bank : ℕ → Option (BitVec width)) (bound lower : ℕ)
    (rows : List (Row width)) (hc : checkSorted bank bound lower rows = true) :
    (∀ row ∈ rows, row.1 < bound ∧ bank row.1 = some row.2 ∧ lower < row.2.toNat) ∧
      rows.Pairwise (fun a b => a.2.toNat < b.2.toNat) := by
  induction rows generalizing lower with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp hc
    have hh' : row.1 < bound ∧ bank row.1 = some row.2 ∧ lower < row.2.toNat := of_decide_eq_true hh
    obtain ⟨ht', hs⟩ := ih row.2.toNat ht
    refine ⟨?_, List.pairwise_cons.mpr ⟨fun r hr => (ht' r hr).2.2, hs⟩⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hh'
    · exact ⟨(ht' r hr).1, (ht' r hr).2.1, hh'.2.2.trans (ht' r hr).2.2⟩

private theorem row_eq_of_mask_eq (rows : List (Row width))
    (hs : rows.Pairwise (fun a b => a.2.toNat < b.2.toNat))
    (a b : Row width) (ha : a ∈ rows) (hb : b ∈ rows) (he : a.2 = b.2) : a = b := by
  induction rows with
  | nil => simp at ha
  | cons r rows ih =>
    obtain ⟨hr, ht⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with rfl | hatail
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · rfl
      · have := hr b hbtail
        simp [he] at this
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · have := hr a hatail
        simp [he] at this
      · exact ih ht hatail hbtail

/-- Bounded, distinct IDs with the full bank length cover every valid position. -/
theorem checked_bank_injective (bank : ℕ → Option (BitVec width)) (bound : ℕ)
    (rows : List (Row width)) (hc : checkSorted bank bound 0 rows = true)
    (hlen : rows.length = bound) :
    ∀ i < bound, ∀ j < bound, bank i = bank j → i = j := by
  obtain ⟨hr, hs⟩ := checkSorted_sound bank bound 0 rows hc
  have hn : (rows.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    apply hs.imp_of_mem
    intro a b ha hb hlt he
    have hm : a.2 = b.2 := Option.some.inj (by rw [← (hr a ha).2.1, ← (hr b hb).2.1, he])
    have he' := congrArg BitVec.toNat hm
    omega
  have hsub : (rows.map Prod.fst).toFinset ⊆ Finset.range bound := by
    intro i hi
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    exact Finset.mem_range.mpr (hr r hr').1
  have heq : (rows.map Prod.fst).toFinset = Finset.range bound :=
    Finset.eq_of_subset_of_card_le hsub (by simp [List.toFinset_card_of_nodup hn, hlen])
  intro i hi j hj he
  have getRow (k : ℕ) (hk : k < bound) : ∃ r ∈ rows, r.1 = k := by
    apply List.mem_map.mp
    apply List.mem_toFinset.mp
    rw [heq]
    exact Finset.mem_range.mpr hk
  obtain ⟨a, ha, hai⟩ := getRow i hi
  obtain ⟨b, hb, hbj⟩ := getRow j hj
  have hm : a.2 = b.2 := Option.some.inj (by rw [← (hr a ha).2.1, ← (hr b hb).2.1, hai, hbj, he])
  have hab := row_eq_of_mask_eq rows hs a b ha hb hm
  exact hai.symm.trans ((congrArg Prod.fst hab).trans hbj)

/-- Static-bank injectivity implies distinct mask payloads in an accepted DAG. -/
theorem entries_masks_nodup (bank : ℕ → Option (BitVec width)) (entries : List (Entry width))
    (hc : checkChunk bank 0 entries = true)
    (hinj : ∀ i < entries.length, ∀ j < entries.length, bank i = bank j → i = j) :
    (entries.map Entry.mask).Nodup := by
  obtain ⟨_, ha⟩ := checkChunk_sound bank [] entries (by intro i hi; simp at hi) hc
  apply List.nodup_iff_injective_get.mpr
  intro i j he
  have hi : i.val < entries.length := by simpa using i.isLt
  have hj : j.val < entries.length := by simpa using j.isLt
  apply Fin.ext
  apply hinj i.val hi j.val hj
  rw [ha i.val (by simpa using hi), ha j.val (by simpa using hj)]
  simpa only [List.nil_append, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem j.isLt, List.get_eq_getElem] using congrArg some he

theorem entries_supports_nodup (bank : ℕ → Option (BitVec width)) (entries : List (Entry width))
    (hc : checkChunk bank 0 entries = true)
    (hinj : ∀ i < entries.length, ∀ j < entries.length, bank i = bank j → i = j) :
    ((entries.map Entry.toNode).map DisjointCircuit.Node.support).Nodup := by
  simpa only [List.map_map, Function.comp_def, Entry.toNode] using
    (entries_masks_nodup bank entries hc hinj).map decode_injective

end IntegerMultBounds.Networks.MaskUnique
