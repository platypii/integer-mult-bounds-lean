import IntegerMultBounds.Networks.PairedCircuit
import IntegerMultBounds.Networks.PairedPartition
import IntegerMultBounds.Networks.SupportInterpretation

/-! Actual weighted graph contraction through consecutive pairs. Coarse
vertex cells contain fine internal sources, and coarse edge cells contain
fine crossing sources. Their partition and exclusion identities are proved
on the original source atoms, before interpreting any DAG weights. -/

namespace IntegerMultBounds.Networks.PairedCoarseSupport

open PairedPartition SupportInterpretation

/-- The exact canonical vertex and edge keys of a weighted graph. -/
def atomDomain (points : List ℕ) : Finset (Source ℕ) :=
  points.toFinset.image Source.vertex ∪
    (PairedCircuit.pairs points).toFinset.image (fun p => Source.edge p.1 p.2)

@[simp] theorem vertex_mem_domain (points : List ℕ) (v : ℕ) :
    Source.vertex v ∈ atomDomain points ↔ v ∈ points := by simp [atomDomain]

@[simp] theorem edge_mem_domain (points : List ℕ) (u v : ℕ) :
    Source.edge u v ∈ atomDomain points ↔ (u,v) ∈ PairedCircuit.pairs points := by
  simp [atomDomain, Prod.exists]

theorem mem_pairs_sorted (points : List ℕ) (hs : points.Pairwise (· < ·)) (a b : ℕ) :
    (a,b) ∈ PairedCircuit.pairs points ↔ a ∈ points ∧ b ∈ points ∧ a < b := by
  induction points with
  | nil => simp [PairedCircuit.pairs]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hs
    rw [PairedCircuit.pairs, List.mem_append, List.mem_map, ih hxs]
    simp only [Prod.mk.injEq, List.mem_cons]
    constructor
    · rintro (⟨v, hv, hxa, hvb⟩ | ⟨ha, hb, hab⟩)
      · subst a; subst b
        exact ⟨Or.inl rfl, Or.inr hv, hx v hv⟩
      · exact ⟨Or.inr ha, Or.inr hb, hab⟩
    · rintro ⟨ha, hb, hab⟩
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · omega
        · exact Or.inl ⟨b, hb, rfl, rfl⟩
      · rcases hb with rfl | hb
        · have hh := hx a ha
          omega
        · exact Or.inr ⟨ha, hb, hab⟩

@[simp] theorem edge_mem_range (n u v : ℕ) :
    Source.edge u v ∈ atomDomain (List.range n) ↔ u < v ∧ v < n := by
  rw [edge_mem_domain, mem_pairs_sorted _ List.pairwise_lt_range]
  simp only [List.mem_range]
  omega

def groupSet (points : List ℕ) (i : ℕ) : Finset ℕ :=
  (PairedCircuit.groupAt (PairGrouping.groups points) i).toFinset

theorem groupSet_get (points : List ℕ) (i : ℕ) (hi : i < (PairGrouping.groups points).length) :
    groupSet points i = ((PairGrouping.groups points)[i]).toFinset := by
  simp [groupSet, PairedCircuit.groupAt, List.getElem?_eq_getElem hi]

theorem groupSet_empty (points : List ℕ) (i : ℕ) (hi : (PairGrouping.groups points).length ≤ i) :
    groupSet points i = ∅ := by
  simp [groupSet, PairedCircuit.groupAt, List.getElem?_eq_none hi]

theorem index_lt_of_mem (points : List ℕ) (i v : ℕ) (hv : v ∈ groupSet points i) :
    i < (PairGrouping.groups points).length := by
  by_contra hn
  rw [groupSet_empty points i (by omega)] at hv
  exact Finset.notMem_empty _ hv

theorem exists_group (points : List ℕ) (v : ℕ) (hv : v ∈ points) :
    ∃ i, i < (PairGrouping.groups points).length ∧ v ∈ groupSet points i := by
  obtain ⟨g, hg, hvg⟩ := (PairGrouping.mem_group points v).mpr hv
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
  exact ⟨i, hi, by rw [groupSet_get points i hi, hgi]; exact List.mem_toFinset.mpr hvg⟩

theorem groups_disjoint (points : List ℕ) (hn : points.Nodup) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (groupSet points i) (groupSet points j) := by
  by_cases hi : i < (PairGrouping.groups points).length
  · by_cases hj : j < (PairGrouping.groups points).length
    · rw [groupSet_get points i hi, groupSet_get points j hj]
      apply List.disjoint_toFinset_iff_disjoint.mpr
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) i j hi hj hlt
      · exact (List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) j i hj hi hgt).symm
    · rw [groupSet_empty points j (by omega)]
      exact Finset.disjoint_empty_right _
  · rw [groupSet_empty points i (by omega)]
    exact Finset.disjoint_empty_left _

/-- A proof-only classifier locates each present fine vertex in its unique
actual consecutive pair. It is not an additional graph operation. -/
noncomputable def location (points : List ℕ) (v : ℕ) : ℕ :=
  if hv : v ∈ points then Classical.choose (exists_group points v hv) else 0

theorem location_spec (points : List ℕ) (v : ℕ) (hv : v ∈ points) :
    location points v < (PairGrouping.groups points).length ∧ v ∈ groupSet points (location points v) := by
  simp only [location, dite_eq_left hv]
  exact Classical.choose_spec (exists_group points v hv)

theorem mem_group_iff (points : List ℕ) (hn : points.Nodup) (v i : ℕ) (hv : v ∈ points) :
    v ∈ groupSet points i ↔ location points v = i := by
  constructor
  · intro hi
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint points hn (location points v) i hne)
      (location_spec points v hv).2 hi
  · rintro rfl
    exact (location_spec points v hv).2

noncomputable def classify (points : List ℕ) : Source ℕ → Source ℕ
  | .vertex v => .vertex (location points v)
  | .edge u v => if location points u = location points v then .vertex (location points u)
      else .edge (min (location points u) (location points v)) (max (location points u) (location points v))

/-- Coarse cells retain the actual fine source identifiers. -/
def cell (sources : Finset (Source ℕ)) (points : List ℕ) : Source ℕ → Finset (Source ℕ)
  | .vertex i => confined sources (groupSet points i)
  | .edge i j => bridge sources (groupSet points i) (groupSet points j)

/-- Membership in the concrete coarse cell is precisely the coarse key of
the fine source, not an assumed partition annotation. -/
theorem mem_cell_iff (sources : Finset (Source ℕ)) (points : List ℕ) (hn : points.Nodup)
    (hw : Within sources points.toFinset) (c : Source ℕ)
    (hc : c ∈ atomDomain (List.range (PairGrouping.groups points).length)) (s : Source ℕ) :
    s ∈ cell sources points c ↔ s ∈ sources ∧ classify points s = c := by
  by_cases hs : s ∈ sources
  · have hp := hw s hs
    cases s with
    | vertex v =>
      have hv : v ∈ points := by simpa [endpoints, Finset.singleton_subset_iff] using hp
      cases c with
      | vertex i => simp [cell, mem_confined, endpoints, hs, Finset.singleton_subset_iff,
          mem_group_iff points hn v i hv, classify]
      | edge i j => simp [cell, bridge, classify]
    | edge u v =>
      have hp' : u ∈ points ∧ v ∈ points := by
        simpa [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] using hp
      cases c with
      | vertex i =>
        simp only [cell, mem_confined, endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          hs, true_and, mem_group_iff points hn u i hp'.1, mem_group_iff points hn v i hp'.2, classify]
        split_ifs <;> simp_all
        omega
      | edge i j =>
        have hij := (edge_mem_range _ i j).mp hc
        simp only [cell, bridge, Finset.mem_filter, hs, true_and, decide_eq_true_eq,
          mem_group_iff points hn u i hp'.1, mem_group_iff points hn u j hp'.1,
          mem_group_iff points hn v i hp'.2, mem_group_iff points hn v j hp'.2, classify]
        split_ifs <;> simp_all [min_def, max_def] <;> (try split_ifs) <;> (try simp_all) <;> omega
  · cases c <;> simp [cell, mem_confined, bridge, hs]


theorem groupSet_subset (points : List ℕ) (i : ℕ) :
    groupSet points i ⊆ points.toFinset := by
  intro v hv
  have hi := index_lt_of_mem points i v hv
  rw [groupSet_get points i hi] at hv
  exact List.mem_toFinset.mpr (PairGrouping.group_subset points _
    (List.getElem_mem hi) (List.mem_toFinset.mp hv))

theorem cell_subset (sources : Finset (Source ℕ)) (points : List ℕ) (c : Source ℕ) :
    cell sources points c ⊆ sources := by
  cases c <;> exact Finset.filter_subset _ _

theorem classify_mem (sources : Finset (Source ℕ)) (points : List ℕ)
    (hw : Within sources points.toFinset) (s : Source ℕ) (hs : s ∈ sources) :
    classify points s ∈ atomDomain (List.range (PairGrouping.groups points).length) := by
  have hp := hw s hs
  cases s with
  | vertex v =>
    have hv : v ∈ points := by simpa [endpoints, Finset.singleton_subset_iff] using hp
    simpa [classify] using (location_spec points v hv).1
  | edge u v =>
    have hp' : u ∈ points ∧ v ∈ points := by
      simpa [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] using hp
    have hu := (location_spec points u hp'.1).1
    have hv := (location_spec points v hp'.2).1
    simp only [classify]
    split_ifs with he
    · simpa using hu
    · rw [edge_mem_range]
      omega

theorem cells_disjointOn (sources : Finset (Source ℕ)) (points : List ℕ)
    (hn : points.Nodup) (hw : Within sources points.toFinset) :
    DisjointOn (cell sources points) (atomDomain (List.range (PairGrouping.groups points).length)) := by
  intro c hc d hd hne
  apply Finset.disjoint_left.mpr
  intro s hsc hsd
  have h1 := (mem_cell_iff sources points hn hw c hc s).mp hsc
  have h2 := (mem_cell_iff sources points hn hw d hd s).mp hsd
  exact hne (h1.2.symm.trans h2.2)

theorem interpret_cells (sources : Finset (Source ℕ)) (points : List ℕ)
    (hn : points.Nodup) (hw : Within sources points.toFinset) :
    interpret (cell sources points) (atomDomain (List.range (PairGrouping.groups points).length)) = sources := by
  ext s
  rw [mem_interpret]
  constructor
  · rintro ⟨c, _, hc⟩
    exact cell_subset sources points c hc
  · intro hs
    have hc := classify_mem sources points hw s hs
    exact ⟨classify points s, hc, (mem_cell_iff sources points hn hw _ hc s).mpr ⟨hs, rfl⟩⟩

theorem domain_within (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    Within (atomDomain points) points.toFinset := by
  intro s hm
  cases s with
  | vertex v => simpa [endpoints, Finset.singleton_subset_iff] using hm
  | edge u v =>
    have hp := (mem_pairs_sorted points hs u v).mp ((edge_mem_domain points u v).mp hm)
    simpa [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] using ⟨hp.1, hp.2.1⟩

theorem domain_loopless (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    Loopless (atomDomain points) := by
  intro u v hm
  exact ne_of_lt ((mem_pairs_sorted points hs u v).mp ((edge_mem_domain points u v).mp hm)).2.2


/-- Classification preserves exactly the endpoint group indices. -/
theorem endpoints_classify (points : List ℕ) (s : Source ℕ) :
    endpoints (classify points s) = (endpoints s).image (location points) := by
  cases s with
  | vertex v => simp [classify, endpoints]
  | edge u v =>
    by_cases he : location points u = location points v
    · simp [classify, he, endpoints]
    · by_cases hl : location points u ≤ location points v
      · simp [classify, he, endpoints, min_eq_left hl, max_eq_right hl]
      · have hl' : location points v ≤ location points u := by omega
        simp [classify, he, endpoints, min_eq_right hl', max_eq_left hl', Finset.pair_comm]

theorem mem_groupUnion_iff (points : List ℕ) (hn : points.Nodup) (excluded : Finset ℕ)
    (v : ℕ) (hv : v ∈ points) :
    v ∈ excluded.biUnion (groupSet points) ↔ location points v ∈ excluded := by
  simp only [Finset.mem_biUnion, mem_group_iff points hn v _ hv]
  constructor
  · rintro ⟨i, hi, he⟩
    exact he.symm ▸ hi
  · intro hi
    exact ⟨location points v, hi, rfl⟩

theorem disjoint_classify (points : List ℕ) (hn : points.Nodup) (excluded : Finset ℕ)
    (s : Source ℕ) (hp : endpoints s ⊆ points.toFinset) :
    Disjoint (endpoints (classify points s)) excluded ↔
      Disjoint (endpoints s) (excluded.biUnion (groupSet points)) := by
  rw [endpoints_classify]
  constructor
  · intro hd
    apply Finset.disjoint_left.mpr
    intro v hv he
    exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      ((mem_groupUnion_iff points hn excluded v (List.mem_toFinset.mp (hp hv))).mp he)
  · intro hd
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.disjoint_left.mp hd hv
      ((mem_groupUnion_iff points hn excluded v (List.mem_toFinset.mp (hp hv))).mpr he)

/-- Excluding coarse vertices removes exactly their original fine groups.
This is the contraction identity used by the actual recursive graph. -/
theorem interpret_avoiding (sources : Finset (Source ℕ)) (points : List ℕ)
    (hn : points.Nodup) (hw : Within sources points.toFinset) (excluded : Finset ℕ) :
    interpret (cell sources points)
      (avoiding (atomDomain (List.range (PairGrouping.groups points).length)) excluded) =
        avoiding sources (excluded.biUnion (groupSet points)) := by
  ext s
  rw [mem_interpret, mem_avoiding]
  constructor
  · rintro ⟨c, hc, hsc⟩
    obtain ⟨hc, hd⟩ := (mem_avoiding _ _ _).mp hc
    obtain ⟨hs, he⟩ := (mem_cell_iff sources points hn hw c hc s).mp hsc
    exact ⟨hs, (disjoint_classify points hn excluded s (hw s hs)).mp (he.symm ▸ hd)⟩
  · rintro ⟨hs, hd⟩
    have hc := classify_mem sources points hw s hs
    refine ⟨classify points s, ?_, (mem_cell_iff sources points hn hw _ hc s).mpr ⟨hs, rfl⟩⟩
    exact (mem_avoiding _ _ _).mpr ⟨hc, (disjoint_classify points hn excluded s (hw s hs)).mpr hd⟩

end IntegerMultBounds.Networks.PairedCoarseSupport
