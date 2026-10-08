import IntegerMultBounds.Networks.SharedPointLift

/-! The checked pair-exclusion outputs are exactly the common-point partial
outputs of the global intersection-one map, under the actual source embedding. -/

namespace IntegerMultBounds.Networks.SharedPointOutputMap

open SharedPointLift NeighborCounts SharedPointMap MaskDAG

theorem pairPayload_surjective (n : ℕ) (P : Finset (Fin n)) (hp : P.card = 2) :
    ∃ i : Fin (n.choose 2), pairPayload n i = P := by
  have ordered (a b : Fin n) (hab : a < b) :
      ∃ i : Fin (n.choose 2), pairPayload n i = {a,b} := by
    have hm : (a.val,b.val) ∈ PairedCircuit.pairs (List.range n) :=
      (PairedCoarseSupport.mem_pairs_sorted _ List.pairwise_lt_range _ _).mpr
        ⟨by simp, by simp, hab⟩
    obtain ⟨i, hi⟩ := (PairMask.pairEquiv n).surjective ⟨(a.val,b.val), hm⟩
    have he : PairMask.pairAt n i = (a.val,b.val) := congrArg Subtype.val hi
    refine ⟨i, ?_⟩
    rw [pairPayload_eq_filter]
    ext v
    simp [he, Fin.ext_iff]
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hp
  rcases lt_or_gt_of_ne hab with h | h
  · exact ordered a b h
  · simpa only [Finset.pair_comm] using ordered b a h

/-- Every triple containing the common point is an actual renamed pair input. -/
theorem source_covers (n : ℕ) (c : Fin (n+1)) (T : Triple (n+1)) (hc : c ∈ T.val) :
    ∃ i : Fin (n.choose 2), source (pairPayload n) (pairPayload_card n) c i = T := by
  let P := T.val.erase c
  let Q : Finset (Fin n) := Finset.univ.filter (fun j => c.succAbove j ∈ P)
  have himage : Q.image c.succAbove = P := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
    · intro hx
      have hne : x ≠ c := (Finset.mem_erase.mp hx).1
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hq : Q.card = 2 := by
    rw [← Finset.card_image_of_injective Q Fin.succAbove_right_injective, himage]
    change (T.val.erase c).card = 2
    rw [Finset.card_erase_of_mem hc, T.property]
  obtain ⟨i, hi⟩ := pairPayload_surjective n Q hq
  refine ⟨i, Subtype.ext ?_⟩
  rw [source_val, hi, himage]
  exact Finset.insert_erase hc

/-- The bitmask test is precisely disjointness of the two actual endpoint sets. -/
theorem exclusion_disjoint (n : ℕ) (i j : Fin (n.choose 2)) :
    i ∈ decode (PairMask.exclusion n (PairMask.pairAt n j).1 (PairMask.pairAt n j).2) ↔
      Disjoint (pairPayload n i) (pairPayload n j) := by
  rw [PairMask.mem_exclusion]
  simp [pairPayload, pairLeft, pairRight, Fin.ext_iff]
  aesop

theorem source_intersection (n : ℕ) (c : Fin (n+1)) (i j : Fin (n.choose 2)) :
    (source (pairPayload n) (pairPayload_card n) c i).val ∩
        (source (pairPayload n) (pairPayload_card n) c j).val = {c} ↔
      Disjoint (pairPayload n i) (pairPayload n j) := by
  let P : PairAway c := ⟨(pairPayload n i).image c.succAbove,
    by rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective, pairPayload_card], by simp⟩
  let Q : PairAway c := ⟨(pairPayload n j).image c.succAbove,
    by rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective, pairPayload_card], by simp⟩
  change (insertTriple c P).val ∩ (insertTriple c Q).val = {c} ↔ _
  rw [inserted_intersection c _ (insertTriple_common c Q)]
  change Disjoint P.val ((insert c Q.val).erase c) ↔ _
  rw [Finset.erase_insert Q.property.2]
  exact Finset.disjoint_image Fin.succAbove_right_injective

/-- Exact finite support of every canonical local output after global lifting. -/
theorem lifted_exclusion (n : ℕ) (c : Fin (n+1)) (j : Fin (n.choose 2)) :
    lift (pairPayload n) (pairPayload_card n) c
        (decode (PairMask.exclusion n (PairMask.pairAt n j).1 (PairMask.pairAt n j).2)) =
      Finset.univ.filter (fun T : Triple (n+1) =>
        T.val ∩ (source (pairPayload n) (pairPayload_card n) c j).val = {c}) := by
  ext T
  simp only [lift, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (source_intersection n c i j).mpr ((exclusion_disjoint n i j).mp hi)
  · intro ht
    have hc : c ∈ T.val := by
      have hm : c ∈ T.val ∩ (source (pairPayload n) (pairPayload_card n) c j).val := by
        rw [ht]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hm).1
    obtain ⟨i, rfl⟩ := source_covers n c T hc
    exact ⟨i, (exclusion_disjoint n i j).mpr ((source_intersection n c i j).mp ht), rfl⟩

end IntegerMultBounds.Networks.SharedPointOutputMap
