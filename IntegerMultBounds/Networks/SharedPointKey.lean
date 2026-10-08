import IntegerMultBounds.Networks.SharedPointMap

/-! Exact compressed support keys for common-point circuit sharing. A family
of triples containing a fixed pair is determined by its common vertices and
its union of vertices. Thus the upstream key merges equal linear sums, not
merely equal metadata. No circuit count is asserted here. -/

namespace IntegerMultBounds.Networks.SharedPointKey

open NeighborCounts
variable {h : ℕ}

/-- Vertices present in every triple of an actual source support. -/
def core (support : Finset (Triple h)) : Finset (Fin h) :=
  Finset.univ.filter (fun x => ∀ T ∈ support, x ∈ T.val)

/-- Vertices present in at least one triple of an actual source support. -/
def vertices (support : Finset (Triple h)) : Finset (Fin h) :=
  support.biUnion Subtype.val

@[simp] theorem mem_core (support : Finset (Triple h)) (x : Fin h) :
    x ∈ core support ↔ ∀ T ∈ support, x ∈ T.val := by simp [core]

@[simp] theorem mem_vertices (support : Finset (Triple h)) (x : Fin h) :
    x ∈ vertices support ↔ ∃ T ∈ support, x ∈ T.val := Finset.mem_biUnion

@[simp] theorem core_union (s t : Finset (Triple h)) : core (s ∪ t) = core s ∩ core t := by
  ext x
  simp only [mem_core, Finset.mem_union, Finset.mem_inter]
  aesop

@[simp] theorem vertices_union (s t : Finset (Triple h)) :
    vertices (s ∪ t) = vertices s ∪ vertices t := by
  ext x
  simp only [mem_vertices, Finset.mem_union]
  aesop

@[simp] theorem core_singleton (T : Triple h) : core {T} = T.val := by ext x; simp
@[simp] theorem vertices_singleton (T : Triple h) : vertices {T} = T.val := by ext x; simp

theorem core_subset (support : Finset (Triple h)) (T : Triple h) (hT : T ∈ support) :
    core support ⊆ T.val := fun _ hx => (mem_core _ _).mp hx T hT

theorem subset_vertices (support : Finset (Triple h)) (T : Triple h) (hT : T ∈ support) :
    T.val ⊆ vertices support := fun _ hx => (mem_vertices _ _).mpr ⟨T, hT, hx⟩

/-- Every possible triple containing the fixed pair and using the recorded
union is present. Its unique third vertex occurs in an actual source triple. -/
theorem mem_of_pair_union (support : Finset (Triple h)) (P : Finset (Fin h))
    (hP : P.card = 2) (hp : ∀ S ∈ support, P ⊆ S.val)
    (T : Triple h) (hPT : P ⊆ T.val) (hTv : T.val ⊆ vertices support) : T ∈ support := by
  obtain ⟨x, hxT, hxP⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : P.card < T.val.card)
  obtain ⟨S, hS, hxS⟩ := (mem_vertices support x).mp (hTv hxT)
  have hcard : (insert x P).card = 3 := by simp [hxP, hP]
  have hST : insert x P = T.val := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hxT hPT) (by rw [T.property, hcard])
  have hSS : insert x P = S.val := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hxS (hp S hS)) (by rw [S.property, hcard])
  have he : T = S := Subtype.ext (hST.symm.trans hSS)
  exact he ▸ hS

/-- Two supports with the same fixed pair and vertex union are exactly equal. -/
theorem eq_of_pair_vertices (s t : Finset (Triple h)) (P : Finset (Fin h)) (hP : P.card = 2)
    (hs : ∀ T ∈ s, P ⊆ T.val) (ht : ∀ T ∈ t, P ⊆ T.val)
    (he : vertices s = vertices t) : s = t := by
  apply Finset.Subset.antisymm
  · intro T hT
    apply mem_of_pair_union t P hP ht T (hs T hT)
    rw [← he]
    exact subset_vertices s T hT
  · intro T hT
    apply mem_of_pair_union s P hP hs T (ht T hT)
    rw [he]
    exact subset_vertices t T hT

/-- The exact upstream dictionary key. -/
def key (support : Finset (Triple h)) : Finset (Fin h) × Finset (Fin h) :=
  (core support, vertices support)

/-- The key is injective on the branch where sharing is performed. -/
theorem key_injective (s t : Finset (Triple h)) (hcore : 2 ≤ (core s).card)
    (he : key s = key t) : s = t := by
  obtain ⟨hc, hv⟩ := Prod.mk.inj he
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hcore
  apply eq_of_pair_vertices s t P hPcard
  · intro T hT
    exact hPsub.trans (core_subset s T hT)
  · intro T hT
    rw [hc] at hPsub
    exact hPsub.trans (core_subset t T hT)
  · exact hv

/-- Any support shared between distinct common-point copies falls within
that injective branch, so the compressed interning test loses no such sharing. -/
theorem two_common_points (support : Finset (Triple h)) (c d : Fin h) (hcd : c ≠ d)
    (hc : ∀ T ∈ support, c ∈ T.val) (hd : ∀ T ∈ support, d ∈ T.val) :
    2 ≤ (core support).card := by
  have hsub : ({c, d} : Finset (Fin h)) ⊆ core support := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (mem_core _ _).mpr hc
    · have he := Finset.mem_singleton.mp hx
      subst x
      exact (mem_core _ _).mpr hd
  have hh := Finset.card_le_card hsub
  simpa [hcd] using hh

end IntegerMultBounds.Networks.SharedPointKey
