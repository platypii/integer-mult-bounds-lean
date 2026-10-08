import IntegerMultBounds.Compact.ExactRepair
import IntegerMultBounds.Compact.Density
import IntegerMultBounds.Machine.Reinsert
import IntegerMultBounds.Machine.RadixSort

/-! The assembled exceptional-address repair pipeline (§5, the correction in the
proof of the packed selected-bit lemma). The actual program `S` moves the record
at address `x` to `S x`; the ideal map `T` agrees with `S` off the exceptional
set and preserves it. On the stream in rank order, flag the records at
exceptional addresses, extract them with their destination ranks
`e (T (S⁻¹ q))`, radix sort the extracted records by destination, and reinsert
them into the flagged holes in order. The result is the stream of the ideal
map everywhere. The extracted records are the exceptional addresses, so their
number is the exceptional fraction times the volume and the radix passes
traverse `A · |ℬ| · (R + A)` cells; with the density bound this gives the
written cost expression, at most three volumes. Both concrete packed programs
are instantiated. Tape execution of the scan is not part of this file. -/

namespace IntegerMultBounds.Compact

open Machine.Partition (Record)
open Machine.Reinsert (fill)
open Machine.RadixSort

/-! ### Reinsertion along a filter -/

section Fill

/-- Filling the holes of a flagged list with records indexed by the flagged positions. -/
theorem fill_map_filter {ι : Type*} (l : List ι) (P : ι → Bool) (g h : ι → Record)
    (hg : ∀ i, (g i).key = P i) :
    fill (l.map g) ((l.filter P).map h) = l.map fun i => if P i then h i else g i := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.filter_cons]
    cases hP : P i
    · have hk : (g i).key = false := by rw [hg, hP]
      simp [fill, hk, ih]
    · have hk : (g i).key = true := by rw [hg, hP]
      simp [fill, hk, ih]

end Fill

/-! ### Keys from natural numbers -/

section Keys

variable {β : Type*}

/-- The low `k` bits of a natural key. -/
theorem keyValue_testBit (f : β → ℕ) (k : ℕ) (x : β) :
    keyValue (fun y j => Nat.testBit (f y) j) k x = f x % 2 ^ k := by
  induction k with
  | zero => simp [keyValue, Nat.mod_one]
  | succ k ih =>
    rw [keyValue, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    have h : f x / 2 ^ k % 2 = 0 ∨ f x / 2 ^ k % 2 = 1 := by omega
    rcases h with h | h <;> simp [h]

theorem keyValue_testBit_of_lt (f : β → ℕ) {k : ℕ} {x : β} (hx : f x < 2 ^ k) :
    keyValue (fun y j => Nat.testBit (f y) j) k x = f x := by
  rw [keyValue_testBit, Nat.mod_eq_of_lt hx]

/-- Two permuted lists with the same injective key sequence are equal. -/
theorem eq_of_perm_of_map_eq {γ : Type*} (f : β → γ) :
    ∀ {l₁ l₂ : List β}, l₁.Perm l₂ → l₁.map f = l₂.map f → (l₂.map f).Nodup → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, hp, _, _ => absurd hp.length_eq (by simp)
  | _ :: _, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: l₁, b :: l₂, hp, hm, hn => by
    simp only [List.map_cons, List.cons.injEq] at hm
    simp only [List.map_cons, List.nodup_cons] at hn
    have hab : a = b := by
      have ha : a ∈ b :: l₂ := hp.subset (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with h | h
      · exact h
      · exact absurd (hm.1 ▸ List.mem_map_of_mem h) hn.1
    subst hab
    rw [eq_of_perm_of_map_eq f (List.Perm.cons_inv hp) hm.2 hn.2]

end Keys

/-! ### The abstract pipeline -/

section Abstract

variable {α : Type*} [Fintype α] {M : ℕ} (e : α ≃ Fin M) (S T : Equiv.Perm α)
  (bad : α → Prop) [DecidablePred bad]

/-- The stream in rank order: rank `i` holds the data at address `e.symm i`,
flagged when that address is exceptional. -/
def stream (data : α → List Bool) : List Record :=
  (List.finRange M).map fun i => ⟨decide (bad (e.symm i)), data (e.symm i)⟩

/-- The ranks of the exceptional addresses in increasing order: the holes. -/
def badRanks : List (Fin M) := (List.finRange M).filter fun i => decide (bad (e.symm i))

/-- The destination rank `e (T (S⁻¹ q))` of the record currently at rank `i`. -/
def destRank (i : Fin M) : Fin M := e (T (S.symm (e.symm i)))

/-- The extracted exceptional records of the actual output with their destination
ranks as keys. -/
def extracted (data : α → List Bool) : List (Fin M × Record) :=
  (badRanks e bad).map fun i => (destRank e S T i, ⟨true, data (S.symm (e.symm i))⟩)

/-- Key bits: the binary digits of the destination rank. -/
def keyBit (x : Fin M × Record) (j : ℕ) : Bool := Nat.testBit x.1 j

/-- `k` stable radix passes on the extracted records, least significant bit first. -/
def sortedExtracted (k : ℕ) (data : α → List Bool) : List (Fin M × Record) :=
  sort keyBit k (extracted e S T bad data)

/-- The pipeline: the actual output stream with its holes filled, in order, by the
sorted extracted records. -/
def pipeline (k : ℕ) (data : α → List Bool) : List Record :=
  fill (stream e bad (data ∘ S.symm)) ((sortedExtracted e S T bad k data).map Prod.snd)

variable (hT : ∀ x, bad (T x) ↔ bad x) (agree : ∀ x, ¬bad x → S x = T x)

omit [Fintype α] in
theorem badRanks_nodup : (badRanks e bad).Nodup :=
  (List.nodup_finRange M).filter _

omit [Fintype α] in
theorem mem_badRanks (i : Fin M) : i ∈ badRanks e bad ↔ bad (e.symm i) := by
  simp [badRanks]

omit [Fintype α] in
theorem badRanks_pairwise : (badRanks e bad).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange M).filter _

include hT agree in
omit [Fintype α] [DecidablePred bad] in
/-- The destination map permutes the exceptional ranks. -/
theorem bad_destRank (i : Fin M) : bad (e.symm (destRank e S T i)) ↔ bad (e.symm i) := by
  unfold destRank
  rw [Equiv.symm_apply_apply, hT]
  have h := actual_preserves_bad S T bad hT agree (S.symm (e.symm i))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit [Fintype α] in
theorem destRank_injective : Function.Injective (destRank e S T) := by
  intro i j h
  unfold destRank at h
  simpa using h

include hT agree in
omit [Fintype α] in
/-- The destination ranks of the extracted records are the holes, as a multiset. -/
theorem destRank_badRanks_perm :
    ((badRanks e bad).map (destRank e S T)).Perm (badRanks e bad) := by
  rw [List.perm_ext_iff_of_nodup
    ((badRanks_nodup e bad).map (destRank_injective e S T)) (badRanks_nodup e bad)]
  intro j
  rw [List.mem_map, mem_badRanks]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (bad_destRank e S T bad hT agree i).mpr ((mem_badRanks e bad i).mp hi)
  · intro hj
    refine ⟨e (S (T.symm (e.symm j))), ?_, ?_⟩
    · rw [mem_badRanks, Equiv.symm_apply_apply, actual_preserves_bad S T bad hT agree]
      have h := hT (T.symm (e.symm j))
      rw [Equiv.apply_symm_apply] at h
      exact h.mp hj
    · unfold destRank
      simp

/-- The sorted records: the record destined to hole `j`, holding the data at `T⁻¹`
of that address, for each hole in increasing order. -/
def target (data : α → List Bool) : List (Fin M × Record) :=
  (badRanks e bad).map fun j => (j, ⟨true, data (T.symm (e.symm j))⟩)

include hT agree in
omit [Fintype α] in
theorem extracted_perm_target (data : α → List Bool) :
    (extracted e S T bad data).Perm (target e T bad data) := by
  have h : extracted e S T bad data =
      ((badRanks e bad).map (destRank e S T)).map
        fun j => (j, (⟨true, data (T.symm (e.symm j))⟩ : Record)) := by
    unfold extracted
    rw [List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp [destRank]
  rw [h]
  exact (destRank_badRanks_perm e S T bad hT agree).map _

omit [Fintype α] in
theorem target_pairwise (data : α → List Bool) :
    (target e T bad data).Pairwise fun x y => x.1 < y.1 := by
  unfold target
  rw [List.pairwise_map]
  exact badRanks_pairwise e bad

include hT agree in
omit [Fintype α] in
/-- Radix sorting on at least `log₂ M` bits puts the extracted records into hole
order. -/
theorem sortedExtracted_eq (k : ℕ) (hk : M ≤ 2 ^ k) (data : α → List Bool) :
    sortedExtracted e S T bad k data = target e T bad data := by
  have hperm : (sortedExtracted e S T bad k data).Perm (target e T bad data) :=
    (sort_perm _ _ _).trans (extracted_perm_target e S T bad hT agree data)
  have hkey : ∀ x : Fin M × Record, keyValue keyBit k x = (x.1 : ℕ) := fun x =>
    keyValue_testBit_of_lt (fun y : Fin M × Record => (y.1 : ℕ)) (lt_of_lt_of_le x.1.2 hk)
  have hs₁ : ((sortedExtracted e S T bad k data).map fun x => (x.1 : ℕ)).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    refine (sort_pairwise keyBit k _).imp fun {x y} h => ?_
    rwa [hkey, hkey] at h
  have hs₂ : ((target e T bad data).map fun x => (x.1 : ℕ)).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    exact (target_pairwise e T bad data).imp fun h => by
      exact_mod_cast le_of_lt h
  have hn : ((target e T bad data).map fun x => (x.1 : ℕ)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact (target_pairwise e T bad data).imp fun h => Fin.val_ne_iff.mpr (ne_of_lt h)
  exact eq_of_perm_of_map_eq _ hperm
    (List.Perm.eq_of_sortedLE hs₁ hs₂ (hperm.map _)) hn

include hT agree in
omit [Fintype α] in
/-- The assembled pipeline implements the ideal map everywhere: the output stream is
the ideal stream, with the exceptional addresses still flagged. -/
theorem pipeline_exact (k : ℕ) (hk : M ≤ 2 ^ k) (data : α → List Bool) :
    pipeline e S T bad k data = stream e bad (data ∘ T.symm) := by
  unfold pipeline
  rw [sortedExtracted_eq e S T bad hT agree k hk]
  unfold target stream badRanks
  rw [List.map_map, fill_map_filter _ _ _ _ fun i => rfl]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  by_cases hb : bad (e.symm i)
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, Record.mk.injEq, true_and]
    rw [inverse_agrees_off_bad S T bad hT agree _ hb]

end Abstract

/-! ### Counting the extracted records and the cost expression -/

section Cost

variable {α : Type*} [Fintype α] {M : ℕ} (e : α ≃ Fin M) (S T : Equiv.Perm α)
  (bad : α → Prop) [DecidablePred bad]

/-- The holes are exactly the exceptional addresses. -/
theorem badRanks_length : (badRanks e bad).length = Nat.card {x // bad x} := by
  classical
  rw [← List.toFinset_card_of_nodup (badRanks_nodup e bad)]
  have h : (badRanks e bad).toFinset = Finset.univ.filter fun i => bad (e.symm i) := by
    ext i
    simp [mem_badRanks]
  rw [h, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquiv e.symm fun _ => Iff.rfl)

theorem extracted_length (data : α → List Bool) :
    (extracted e S T bad data).length = Nat.card {x // bad x} := by
  rw [extracted, List.length_map, badRanks_length]

/-- The `k` radix passes traverse at most `k · |ℬ| · w` for records of weight at most
`w`. -/
theorem sort_traversed_le (data : α → List Bool) (k : ℕ) (weight : Fin M × Record → ℕ)
    (w : ℕ) (hw : ∀ x ∈ extracted e S T bad data, weight x ≤ w) :
    traversedVolume keyBit weight k (extracted e S T bad data) ≤
      k * (Nat.card {x // bad x} * w) := by
  rw [← extracted_length e S T bad data]
  exact traversedVolume_le _ _ _ _ _ hw

omit [Fintype α] in
/-- The number of extracted records is the exceptional fraction times the volume. -/
theorem card_bad_eq_fraction (good : α → Prop) (hpos : 0 < (Nat.card α : ℝ)) :
    (Nat.card {x // ¬good x} : ℝ) = badFraction good * Nat.card α := by
  unfold badFraction
  field_simp

/-- The written repair cost expression, with the extracted count in place of the
density term, is at most three volumes once the density is small enough. -/
theorem pipeline_cost_le (good : α → Prop) [DecidablePred good] (data : α → List Bool)
    (R A δ : ℝ) (hpos : 0 < (Nat.card α : ℝ)) (hR : 0 ≤ R) (hA : 0 ≤ A) (hAR : A ≤ R)
    (hsetup : A ^ 3 ≤ R) (hδ : 0 ≤ δ) (hfrac : badFraction good ≤ δ)
    (hdensity : δ * A ≤ 1 / 2) :
    (Nat.card α : ℝ) * R + Nat.card α * A ^ 3 +
        ((extracted e S T (fun x => ¬good x) data).length : ℝ) * A * (R + A) ≤
      3 * (Nat.card α * R) := by
  rw [extracted_length, card_bad_eq_fraction good hpos]
  have h := repair_cost_linear (Nat.card α) R A δ hpos.le hR hA hδ hAR hsetup hdensity
  have hB : badFraction good * Nat.card α * A * (R + A) ≤ δ * Nat.card α * A * (R + A) := by
    gcongr
  linarith

end Cost

/-! ### The two concrete packed programs -/

section Concrete

variable (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)

/-- The early packed program's exceptional repair implements the ideal selected-bit
toggle on the whole stream. -/
theorem early_pipeline_exact {M : ℕ} (e : EarlyAddress B L zs.length ≃ Fin M) (k : ℕ)
    (hk : M ≤ 2 ^ k) (data : EarlyAddress B L zs.length → List Bool) :
    pipeline e (packedEarlyPerm (2 * L) B (by omega) (by omega) zs) (earlyIdeal B L hL zs hz)
        (fun y => ¬earlyGood B L zs.length y) k data =
      stream e (fun y => ¬earlyGood B L zs.length y) (data ∘ (earlyIdeal B L hL zs hz).symm) :=
  pipeline_exact e _ _ _ (fun y => not_congr (earlyIdeal_preserves_good B L hL zs hz y))
    (fun y hy => early_program_agrees_on_good B L hB hL zs hz y (not_not.mp hy)) k hk data

/-- The late packed program's exceptional repair implements the ideal selected-bit
toggle on the whole stream. -/
theorem late_pipeline_exact {M : ℕ} (e : LateAddress B L zs.length ≃ Fin M) (k : ℕ)
    (hk : M ≤ 2 ^ k) (data : LateAddress B L zs.length → List Bool) :
    pipeline e (packedLatePerm (2 * L) B (by omega) (by omega) zs) (lateIdeal B L hL zs hz)
        (fun y => ¬lateGood B L zs.length y) k data =
      stream e (fun y => ¬lateGood B L zs.length y) (data ∘ (lateIdeal B L hL zs hz).symm) :=
  pipeline_exact e _ _ _ (fun y => not_congr (lateIdeal_preserves_good B L hL zs hz y))
    (fun y hy => late_program_agrees_on_good B L hB hL zs hz y (not_not.mp hy)) k hk data

/-- Under the dyadic cutoff, the late program's extracted records are at most the
uniform density `5 / (128 p³)` times the volume. -/
theorem late_extracted_le (p : ℝ) (n ell K : ℕ) (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p)
    (hell : p ≤ (2 : ℝ) ^ ell) (hK : 8 * ell + 16 ≤ K) {M : ℕ}
    (e : LateAddress ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n ≃ Fin M)
    (S T : Equiv.Perm (LateAddress ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n))
    (data : LateAddress ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n → List Bool) :
    ((extracted e S T (fun y => ¬lateGood ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n y)
        data).length : ℝ) ≤
      min 1 (5 / (128 * p ^ 3)) *
        Nat.card (LateAddress ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n) := by
  have hfrac := (dyadic_actual_repair_density p n ell K hp hn hell hK).2
  have hpos : 0 < (Nat.card (LateAddress ((2 : ℤ) ^ (4 * ell + 6)) ((2 : ℤ) ^ (K - 1)) n) : ℝ) := by
    rw [late_total_real _ _ (by positivity) (by positivity)]
    positivity
  rw [extracted_length, card_bad_eq_fraction _ hpos]
  gcongr

end Concrete

end IntegerMultBounds.Compact
