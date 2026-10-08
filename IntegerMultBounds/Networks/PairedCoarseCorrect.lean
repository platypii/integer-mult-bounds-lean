import IntegerMultBounds.Networks.PairedGraphSpec
import IntegerMultBounds.Networks.SupportInterpretation
import IntegerMultBounds.Networks.PairedCoarseSupport

/-! Validity and exact source supports of the literal coarse graph constructors.
These proofs concern the actual persistent DAG and ordered association tables. -/

namespace IntegerMultBounds.Networks.PairedCoarseCorrect

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect

variable {ι : Type*} [DecidableEq ι]

def edgeQuery (groups : List (List ℕ)) (edges : EdgeTable) (p : ℕ × ℕ) : List Ref :=
  crossRefs edges (groupAt groups p.1) (groupAt groups p.2)

def weightQuery (groups : List (List ℕ)) (edges : EdgeTable) (weights : WeightTable) (i : ℕ) : List Ref :=
  (groupAt groups i).map (lookup weights) ++
    (pairs (groupAt groups i)).map (fun p => edgeLookup edges p.1 p.2)

/-- Actual coarse-edge construction preserves every old node and records the
balanced sum of each ordered cross-group query under its coarse pair key. -/
theorem coarseEdges_built (nodes : List (Node ι)) (groups : List (List ℕ)) (edges : EdgeTable)
    (hv : Valid nodes)
    (hr : ∀ p ∈ pairs (List.range groups.length), RefsValid nodes (edgeQuery groups edges p))
    (hd : ∀ p ∈ pairs (List.range groups.length), DisjointRefs nodes (edgeQuery groups edges p)) :
    Valid (coarseEdges nodes groups edges).1 ∧
      Extends nodes (coarseEdges nodes groups edges).1 ∧
      TableSpec (fun p => supports nodes (edgeQuery groups edges p))
        (pairs (List.range groups.length))
        (coarseEdges nodes groups edges).1 (coarseEdges nodes groups edges).2 :=
  mapTotals_correct nodes _ (edgeQuery groups edges) hv hr hd

/-- Actual coarse weights build original vertex weights before internal edge
weights, preserving the upstream balanced total's evaluation order. -/
theorem coarseWeights_built (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hv : Valid nodes)
    (hr : ∀ i ∈ List.range groups.length, RefsValid nodes (weightQuery groups edges weights i))
    (hd : ∀ i ∈ List.range groups.length, DisjointRefs nodes (weightQuery groups edges weights i)) :
    Valid (coarseWeights nodes groups edges weights).1 ∧
      Extends nodes (coarseWeights nodes groups edges weights).1 ∧
      TableSpec (fun i => supports nodes (weightQuery groups edges weights i))
        (List.range groups.length)
        (coarseWeights nodes groups edges weights).1 (coarseWeights nodes groups edges weights).2 :=
  mapTotals_correct nodes _ (weightQuery groups edges weights) hv hr hd

open PairedPartition

/-- Tag the actual edge and weight entries without changing their payload order. -/
def atomTable (edges : EdgeTable) (weights : WeightTable) : List (Source ℕ × Ref) :=
  edges.map (fun e => (Source.edge e.1.1 e.1.2, e.2)) ++
    weights.map (fun w => (Source.vertex w.1, w.2))

/-- The canonical fine graph atom order: edges, then vertex weights. -/
def atomKeys (points : List ℕ) : List (Source ℕ) :=
  (pairs points).map (fun p => Source.edge p.1 p.2) ++ points.map Source.vertex

def atomRef (edges : EdgeTable) (weights : WeightTable) (a : Source ℕ) : Ref :=
  lookup (atomTable edges weights) a

def atomSupport (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable)
    (a : Source ℕ) : Finset ι := refSupport nodes (atomRef edges weights a)

@[simp] theorem atomTable_values (edges : EdgeTable) (weights : WeightTable) :
    (atomTable edges weights).map Prod.snd = graphRefs edges weights := by
  simp [atomTable, graphRefs, List.map_map, Function.comp_def]

@[simp] theorem atomRef_vertex (edges : EdgeTable) (weights : WeightTable) (v : ℕ) :
    atomRef edges weights (.vertex v) = lookup weights v := by
  induction edges with
  | nil =>
    induction weights with
    | nil => rfl
    | cons w ws ih =>
      by_cases h : w.1 = v <;> simp_all [atomRef, atomTable, lookup]
  | cons e es ih => simpa [atomRef, atomTable, lookup] using ih

@[simp] theorem atomRef_edge (edges : EdgeTable) (weights : WeightTable) (u v : ℕ) :
    atomRef edges weights (.edge u v) = lookup edges (u, v) := by
  induction edges with
  | nil =>
    induction weights with
    | nil => rfl
    | cons w ws ih => simpa [atomRef, atomTable, lookup] using ih
  | cons e es ih =>
    by_cases h : e.1 = (u, v)
    · simp [atomRef, atomTable, lookup, h]
    · have hh : ¬(e.1.1 = u ∧ e.1.2 = v) := by simpa only [Prod.ext_iff] using h
      simpa [atomRef, atomTable, lookup, h, hh] using ih

omit [DecidableEq ι] in
/-- A present key's executable lookup is one of the table's literal entries. -/
theorem lookup_mem {K : Type*} [DecidableEq K] (table : List (K × Ref))
    (key : K) (hk : key ∈ table.map Prod.fst) : (key, lookup table key) ∈ table := by
  induction table with
  | nil => simp at hk
  | cons e es ih =>
    by_cases h : e.1 = key
    · simp [lookup, h, Prod.ext_iff]
    · have hk' : key ∈ es.map Prod.fst := by simpa [h, Ne.symm h] using hk
      simp [lookup_cons_ne es key e.1 e.2 h, ih hk']

/-- The source names are exactly the canonical graph domain, irrespective of
association-table insertion order. -/
theorem atomTable_keys {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    List.Perm ((atomTable edges weights).map Prod.fst) (atomKeys points) := by
  have he := hg.edge_keys.map (fun p => Source.edge p.1 p.2)
  have hw := hg.weight_keys.map Source.vertex
  simpa [atomTable, atomKeys, List.map_map, Function.comp_def] using he.append hw

/-- Every active fine atom has an actual valid lookup reference. -/
theorem atomRef_valid {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (a : Source ℕ) (ha : a ∈ atomKeys points) : RefValid nodes (atomRef edges weights a) := by
  have hm := lookup_mem (atomTable edges weights) a ((atomTable_keys hg).mem_iff.mpr ha)
  apply hg.refsValid
  rw [← atomTable_values]
  exact List.mem_map.mpr ⟨_, hm, rfl⟩

/-- Distinct named fine atoms inherit disjoint actual payload supports from
the input graph, including the case of repeated zero references. -/
theorem atomSupport_disjoint {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (a b : Source ℕ) (ha : a ∈ atomKeys points) (hb : b ∈ atomKeys points) (hne : a ≠ b) :
    Disjoint (atomSupport nodes edges weights a) (atomSupport nodes edges weights b) := by
  have hd : (atomTable edges weights).Pairwise
      (fun x y => Disjoint (refSupport nodes x.2) (refSupport nodes y.2)) := by
    have h0 := hg.disjoint
    change (graphRefs edges weights).Pairwise (fun l r => Disjoint (refSupport nodes l) (refSupport nodes r)) at h0
    rw [← atomTable_values] at h0
    exact (List.pairwise_map (f := Prod.snd) (R := fun l r : Ref =>
      Disjoint (refSupport nodes l) (refSupport nodes r))).mp h0
  let : Std.Symm (fun x y : Source ℕ × Ref => Disjoint (refSupport nodes x.2) (refSupport nodes y.2)) :=
    ⟨fun _ _ h => h.symm⟩
  have hm (c : Source ℕ) (hc : c ∈ atomKeys points) :=
    lookup_mem (atomTable edges weights) c ((atomTable_keys hg).mem_iff.mpr hc)
  exact hd.forall (hm a ha) (hm b hb) (fun h => hne (congrArg Prod.fst h))

/-- Any duplicate-free sublist of active atom names gives valid disjoint
references, regardless of query order or interned zero references. -/
theorem atomRefs_ready {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (atoms : List (Source ℕ)) (ha : atoms ⊆ atomKeys points) (hn : atoms.Nodup) :
    RefsValid nodes (atoms.map (atomRef edges weights)) ∧
      DisjointRefs nodes (atoms.map (atomRef edges weights)) := by
  constructor
  · intro r hr
    obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hr
    exact atomRef_valid hg a (ha ham)
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ hn
    intro a b ham hbm hne
    exact atomSupport_disjoint hg a b (ha ham) (ha hbm) hne

@[simp] theorem vertex_mem_atomKeys (points : List ℕ) (v : ℕ) :
    Source.vertex v ∈ atomKeys points ↔ v ∈ points := by simp [atomKeys]

@[simp] theorem edge_mem_atomKeys (points : List ℕ) (u v : ℕ) :
    Source.edge u v ∈ atomKeys points ↔ (u, v) ∈ pairs points := by
  simp [atomKeys, Prod.exists]

/-- Every literal consecutive group is an ordered sublist of the input. -/
theorem groupAt_sublist (points : List ℕ) (i : ℕ) :
    List.Sublist (groupAt (PairGrouping.groups points) i) points := by
  by_cases hi : i < (PairGrouping.groups points).length
  · have h := List.sublist_flatten_of_mem (List.getElem_mem hi)
    simpa [groupAt, List.getElem?_eq_getElem hi] using h
  · simp [groupAt, List.getElem?_eq_none (by omega : (PairGrouping.groups points).length ≤ i)]

/-- Canonical atom naming matches the sorted lookup used by the executable. -/
def edgeAtom (p : ℕ × ℕ) : Source ℕ := Source.edge (min p.1 p.2) (max p.1 p.2)

def crossAtoms (left right : List ℕ) : List (Source ℕ) := (left.product right).map edgeAtom

def weightAtoms (group : List ℕ) : List (Source ℕ) :=
  group.map Source.vertex ++ (pairs group).map edgeAtom

@[simp] theorem crossAtoms_refs (edges : EdgeTable) (weights : WeightTable) (left right : List ℕ) :
    (crossAtoms left right).map (atomRef edges weights) = crossRefs edges left right := by
  simp [crossAtoms, crossRefs, List.product, List.map_flatMap, List.map_map, Function.comp_def,
    edgeAtom]
  rfl

@[simp] theorem weightAtoms_refs (edges : EdgeTable) (weights : WeightTable) (group : List ℕ) :
    (weightAtoms group).map (atomRef edges weights) =
      group.map (lookup weights) ++ (pairs group).map (fun p => edgeLookup edges p.1 p.2) := by
  simp [weightAtoms, List.map_map, Function.comp_def, edgeAtom, edgeLookup]

private theorem edgeAtom_injective_on (left right : List ℕ) (hd : left.Disjoint right)
    (p q : ℕ × ℕ) (hp : p ∈ left.product right) (hq : q ∈ left.product right)
    (he : edgeAtom p = edgeAtom q) : p = q := by
  have hp' := List.mem_product.mp hp
  have hq' := List.mem_product.mp hq
  have hne : p.1 ≠ q.2 := fun h => List.disjoint_left.mp hd hp'.1 (h ▸ hq'.2)
  have he' := Source.edge.inj he
  have h1 : p.1 = q.1 := by omega
  apply Prod.ext h1
  omega

theorem crossAtoms_nodup (left right : List ℕ) (hl : left.Nodup) (hr : right.Nodup)
    (hd : left.Disjoint right) : (crossAtoms left right).Nodup :=
  List.Nodup.map_on (fun p hp q hq => edgeAtom_injective_on left right hd p q hp hq) (hl.product hr)

theorem edgeAtom_mem (points : List ℕ) (hs : points.Pairwise (· < ·)) (a b : ℕ)
    (ha : a ∈ points) (hb : b ∈ points) (hne : a ≠ b) : edgeAtom (a, b) ∈ atomKeys points := by
  rw [edgeAtom, edge_mem_atomKeys, pairs_mem points hs]
  rcases le_total a b with h | h
  · simp only [min_eq_left h, max_eq_right h]
    exact ⟨ha, hb, by omega⟩
  · simp only [min_eq_right h, max_eq_left h]
    exact ⟨hb, ha, by omega⟩

theorem crossAtoms_subset (points left right : List ℕ) (hs : points.Pairwise (· < ·))
    (hl : left ⊆ points) (hr : right ⊆ points) (hd : left.Disjoint right) :
    crossAtoms left right ⊆ atomKeys points := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have hp' := List.mem_product.mp hp
  apply edgeAtom_mem points hs p.1 p.2 (hl hp'.1) (hr hp'.2)
  intro he
  exact List.disjoint_left.mp hd hp'.1 (he ▸ hp'.2)

theorem weightAtoms_nodup (group : List ℕ) (hs : group.Pairwise (· < ·)) :
    (weightAtoms group).Nodup := by
  have he : (pairs group).map edgeAtom = (pairs group).map (fun p => Source.edge p.1 p.2) := by
    apply List.map_congr_left
    intro p hp
    have hlt := ((pairs_mem group hs p.1 p.2).mp hp).2.2
    simp [edgeAtom, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
  rw [weightAtoms, he, List.nodup_append]
  have hn : group.Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  refine ⟨hn.map (fun _ _ h => Source.vertex.inj h),
    (pairs_nodup group hs).map (fun p q h => Prod.ext (Source.edge.inj h).1 (Source.edge.inj h).2), ?_⟩
  intro a ha b hb hab
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hb
  cases hab

theorem weightAtoms_subset (points group : List ℕ) (hs : points.Pairwise (· < ·))
    (hg : List.Sublist group points) : weightAtoms group ⊆ atomKeys points := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact (vertex_mem_atomKeys points v).mpr (hg.subset hv)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    have hh := (pairs_mem group (hs.sublist hg) p.1 p.2).mp hp
    exact edgeAtom_mem points hs p.1 p.2 (hg.subset hh.1) (hg.subset hh.2.1) (Nat.ne_of_lt hh.2.2)

/-- The concrete cross-query atom set is exactly the fine-source bridge. -/
theorem crossAtoms_set (points left right : List ℕ) (hs : points.Pairwise (· < ·))
    (hl : left ⊆ points) (hr : right ⊆ points) (hd : left.Disjoint right) :
    (crossAtoms left right).toFinset =
      bridge (atomKeys points).toFinset left.toFinset right.toFinset := by
  ext s
  cases s with
  | vertex v => simp [crossAtoms, edgeAtom, bridge]
  | edge u v =>
    simp only [List.mem_toFinset, crossAtoms, List.mem_map, edgeAtom,
      Source.edge.injEq, bridge, Finset.mem_filter, List.mem_toFinset, edge_mem_atomKeys,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a,b⟩, hp, hmin, hmax⟩
      obtain ⟨ha,hb⟩ := List.mem_product.mp hp
      have hne : a ≠ b := fun h => List.disjoint_left.mp hd ha (h ▸ hb)
      have hm := edgeAtom_mem points hs a b (hl ha) (hr hb) hne
      have huv : (u,v) ∈ pairs points := by
        simpa only [edgeAtom, hmin, hmax, edge_mem_atomKeys] using hm
      refine ⟨huv, ?_⟩
      rcases le_total a b with h | h
      · have hu : a = u := by simpa [min_eq_left h] using hmin
        have hv : b = v := by simpa [max_eq_right h] using hmax
        exact Or.inl ⟨hu ▸ ha, hv ▸ hb⟩
      · have hu : b = u := by simpa [min_eq_right h] using hmin
        have hv : a = v := by simpa [max_eq_left h] using hmax
        exact Or.inr ⟨hv ▸ ha, hu ▸ hb⟩
    · rintro ⟨hp, hm⟩
      have huv := ((pairs_mem points hs u v).mp hp).2.2
      rcases hm with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact ⟨(u,v), List.mem_product.mpr ⟨hu,hv⟩, min_eq_left (le_of_lt huv), max_eq_right (le_of_lt huv)⟩
      · exact ⟨(v,u), List.mem_product.mpr ⟨hv,hu⟩, min_eq_right (le_of_lt huv), max_eq_left (le_of_lt huv)⟩

/-- Internal edge atoms and vertex weights are exactly a confined fine-source cell. -/
theorem weightAtoms_set (points group : List ℕ) (hs : points.Pairwise (· < ·))
    (hg : List.Sublist group points) :
    (weightAtoms group).toFinset = confined (atomKeys points).toFinset group.toFinset := by
  have he : (pairs group).map edgeAtom = (pairs group).map (fun p => Source.edge p.1 p.2) := by
    apply List.map_congr_left
    intro p hp
    have hlt := ((pairs_mem group (hs.sublist hg) p.1 p.2).mp hp).2.2
    simp [edgeAtom, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
  ext s
  cases s with
  | vertex v =>
    simp only [weightAtoms, he, mem_confined, endpoints, Finset.singleton_subset_iff]
    simp
    exact fun h => hg.subset h
  | edge u v =>
    simp only [weightAtoms, he, List.mem_toFinset, List.mem_append, List.mem_map,
      Source.edge.injEq, mem_confined, edge_mem_atomKeys,
      endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff, List.mem_toFinset]
    constructor
    · rintro (h | ⟨p, hp, hp1, hp2⟩)
      · obtain ⟨_, _, h⟩ := h; cases h
      · obtain ⟨a,b⟩ := p
        simp only at hp1 hp2
        subst a; subst b
        have hm := (pairs_mem group (hs.sublist hg) u v).mp hp
        exact ⟨(pairs_mem points hs u v).mpr ⟨hg.subset hm.1, hg.subset hm.2.1, hm.2.2⟩, hm.1, hm.2.1⟩
    · rintro ⟨hp, hu, hv⟩
      exact Or.inr ⟨(u,v), (pairs_mem group (hs.sublist hg) u v).mpr
        ⟨hu, hv, ((pairs_mem points hs u v).mp hp).2.2⟩, rfl, rfl⟩

theorem groupAt_disjoint (points : List ℕ) (hn : points.Nodup) (i j : ℕ) (hne : i ≠ j) :
    (groupAt (PairGrouping.groups points) i).Disjoint (groupAt (PairGrouping.groups points) j) := by
  by_cases hi : i < (PairGrouping.groups points).length
  · by_cases hj : j < (PairGrouping.groups points).length
    · simp only [groupAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
      rcases lt_or_gt_of_ne hne with h | h
      · exact List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) i j hi hj h
      · exact (List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) j i hj hi h).symm
    · simp [groupAt, List.getElem?_eq_none (by omega : (PairGrouping.groups points).length ≤ j)]
  · simp [groupAt, List.getElem?_eq_none (by omega : (PairGrouping.groups points).length ≤ i)]

theorem edgeQuery_ready {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (p : ℕ × ℕ) (hp : p ∈ pairs (List.range (PairGrouping.groups points).length)) :
    RefsValid nodes (edgeQuery (PairGrouping.groups points) edges p) ∧
      DisjointRefs nodes (edgeQuery (PairGrouping.groups points) edges p) := by
  have hl := groupAt_sublist points p.1
  have hr := groupAt_sublist points p.2
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hlt := ((pairs_mem _ List.pairwise_lt_range p.1 p.2).mp hp).2.2
  have hd := groupAt_disjoint points hn p.1 p.2 (Nat.ne_of_lt hlt)
  have hh := atomRefs_ready hg _
    (crossAtoms_subset points _ _ hg.ordered hl.subset hr.subset hd)
    (crossAtoms_nodup _ _ (hn.sublist hl) (hn.sublist hr) hd)
  simpa only [crossAtoms_refs, edgeQuery] using hh

theorem weightQuery_ready {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (i : ℕ) : RefsValid nodes (weightQuery (PairGrouping.groups points) edges weights i) ∧
      DisjointRefs nodes (weightQuery (PairGrouping.groups points) edges weights i) := by
  have hi := groupAt_sublist points i
  have hh := atomRefs_ready hg _ (weightAtoms_subset points _ hg.ordered hi)
    (weightAtoms_nodup _ (hg.ordered.sublist hi))
  simpa only [weightAtoms_refs, weightQuery] using hh

/-- Both literal coarse passes have exact original-state support tables, and
all coarse references remain valid after the later weight pass. -/
theorem coarse_builds {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    Valid cw.1 ∧ Extends nodes cw.1 ∧
      TableSpec (fun p => supports nodes (edgeQuery groups edges p))
        (pairs (List.range groups.length)) cw.1 ce.2 ∧
      TableSpec (fun i => supports nodes (weightQuery groups edges weights i))
        (List.range groups.length) cw.1 cw.2 := by
  let groups := PairGrouping.groups points
  let ce := coarseEdges nodes groups edges
  let cw := coarseWeights ce.1 groups edges weights
  have he := coarseEdges_built nodes groups edges hg.valid
    (fun p hp => (edgeQuery_ready hg p hp).1) (fun p hp => (edgeQuery_ready hg p hp).2)
  have hw := coarseWeights_built ce.1 groups edges weights he.1
    (fun i _ => DisjointExclusion.refsValid_extends he.2.1 (weightQuery_ready hg i).1)
    (fun i _ => DisjointExclusion.disjointRefs_extends he.2.1 _
      (weightQuery_ready hg i).1 (weightQuery_ready hg i).2)
  refine ⟨hw.1, extends_trans he.2.1 hw.2.1, tableSpec_extends _ _ hw.2.1 he.2.2, ?_⟩
  have hh := hw.2.2
  have hsup : (fun i => supports ce.1 (weightQuery groups edges weights i)) =
      (fun i => supports nodes (weightQuery groups edges weights i)) := by
    funext i
    exact DisjointExclusion.supports_extends he.2.1 _ (weightQuery_ready hg i).1
  rwa [hsup] at hh

/-- Finite atom interpretation equals the actual list-support accumulation. -/
theorem supports_atomRefs (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable)
    (atoms : List (Source ℕ)) :
    supports nodes (atoms.map (atomRef edges weights)) =
      SupportInterpretation.interpret (atomSupport nodes edges weights) atoms.toFinset := by
  induction atoms with
  | nil => simp [supports]
  | cons a atoms ih => simp [supports, ih, atomSupport]

theorem atomKeys_nodup (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    (atomKeys points).Nodup := by
  have hn : points.Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  rw [atomKeys, List.nodup_append]
  refine ⟨(pairs_nodup points hs).map
    (fun p q h => Prod.ext (Source.edge.inj h).1 (Source.edge.inj h).2),
    hn.map (fun _ _ h => Source.vertex.inj h), ?_⟩
  intro a ha b hb hab
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
  cases hab

omit [DecidableEq ι] in
theorem tableSpec_refSupports {K : Type*} (support : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) (ht : TableSpec support keys nodes table) :
    table.map (fun e => refSupport nodes e.2) = keys.map support := by
  induction ht with
  | nil => rfl
  | cons h hs ih => simp [h.2.2, ih]

omit [DecidableEq ι] in
theorem tableSpec_refsValid {K : Type*} (support : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) (ht : TableSpec support keys nodes table) :
    RefsValid nodes (table.map Prod.snd) := by
  induction ht with
  | nil => simp [RefsValid]
  | cons h hs ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.2.1
    · exact ih r hr

omit [DecidableEq ι] in
theorem tableSpec_mapKeys {K J : Type*} (support : J → Finset ι) (f : K → J)
    (keys : List K) (nodes : List (Node ι)) (table : List (K × Ref))
    (ht : TableSpec (fun k => support (f k)) keys nodes table) :
    TableSpec support (keys.map f) nodes (table.map (fun e => (f e.1, e.2))) := by
  induction ht with
  | nil => exact .nil
  | cons h hs ih => exact .cons ⟨congrArg f h.1, h.2⟩ ih

omit [DecidableEq ι] in
theorem tableSpec_atomTable (support : Source ℕ → Finset ι) (points : List ℕ)
    (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable)
    (he : TableSpec (fun p => support (.edge p.1 p.2)) (pairs points) nodes edges)
    (hw : TableSpec (fun v => support (.vertex v)) points nodes weights) :
    TableSpec support (atomKeys points) nodes (atomTable edges weights) :=
  List.rel_append (tableSpec_mapKeys support (fun p : ℕ × ℕ => Source.edge p.1 p.2) _ _ _ he)
    (tableSpec_mapKeys support Source.vertex _ _ _ hw)

/-- Exact semantic tables over disjoint named cells establish the complete
recursive graph invariant, rather than merely individual output validity. -/
theorem graphReady_of_atomTable (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (support : Source ℕ → Finset ι)
    (hv : Valid nodes) (hs : points.Pairwise (· < ·))
    (he : TableSpec (fun p => support (.edge p.1 p.2)) (pairs points) nodes edges)
    (hw : TableSpec (fun v => support (.vertex v)) points nodes weights)
    (hd : ∀ a ∈ atomKeys points, ∀ b ∈ atomKeys points, a ≠ b → Disjoint (support a) (support b)) :
    GraphReady nodes points edges weights := by
  have ht := tableSpec_atomTable support points nodes edges weights he hw
  refine ⟨hv, hs, ?_, ?_, ?_, ?_⟩
  · rw [tableSpec_keys _ _ _ _ he]
  · rw [tableSpec_keys _ _ _ _ hw]
  · rw [← atomTable_values]
    exact tableSpec_refsValid _ _ _ _ ht
  · have hkeys : (atomKeys points).Pairwise (fun a b => Disjoint (support a) (support b)) :=
      List.Pairwise.imp_of_mem (fun {a b} ha hb hne => hd a ha b hb hne) (atomKeys_nodup points hs)
    have hout : ((atomTable edges weights).map (fun e => refSupport nodes e.2)).Pairwise Disjoint := by
      rw [tableSpec_refSupports _ _ _ _ ht]
      exact (List.pairwise_map (f := support) (R := Disjoint)).mpr hkeys
    have hrefs : ((atomTable edges weights).map Prod.snd).Pairwise
        (fun a b => Disjoint (refSupport nodes a) (refSupport nodes b)) := by
      apply (List.pairwise_map (f := refSupport nodes) (R := Disjoint)).mp
      simpa only [List.map_map, Function.comp_def] using hout
    simpa only [DisjointRefs, atomTable_values] using hrefs

/-- The graph invariant supplies the support interpretation's disjoint domain
hypothesis for every weighted fine atom. -/
theorem atomSupport_disjointOn {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    SupportInterpretation.DisjointOn (atomSupport nodes edges weights) (atomKeys points).toFinset := by
  intro a ha b hb hne
  exact atomSupport_disjoint hg a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hne

@[simp] theorem atomKeys_domain (points : List ℕ) :
    (atomKeys points).toFinset = PairedCoarseSupport.atomDomain points := by
  ext s
  cases s <;> simp

/-- Actual fine payloads interpreted through a coarse source cell. -/
def coarseSupport (nodes : List (Node ι)) (points : List ℕ) (edges : EdgeTable) (weights : WeightTable)
    (c : Source ℕ) : Finset ι :=
  SupportInterpretation.interpret (atomSupport nodes edges weights)
    (PairedCoarseSupport.cell (PairedCoarseSupport.atomDomain points) points c)

theorem edgeQuery_support {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (p : ℕ × ℕ) (hp : p ∈ pairs (List.range (PairGrouping.groups points).length)) :
    supports nodes (edgeQuery (PairGrouping.groups points) edges p) =
      coarseSupport nodes points edges weights (.edge p.1 p.2) := by
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hlt := ((pairs_mem _ List.pairwise_lt_range p.1 p.2).mp hp).2.2
  rw [edgeQuery, ← crossAtoms_refs edges weights, supports_atomRefs,
    crossAtoms_set points _ _ hg.ordered (groupAt_sublist points p.1).subset
      (groupAt_sublist points p.2).subset (groupAt_disjoint points hn p.1 p.2 (Nat.ne_of_lt hlt)),
    atomKeys_domain]
  rfl

theorem weightQuery_support {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) (i : ℕ) :
    supports nodes (weightQuery (PairGrouping.groups points) edges weights i) =
      coarseSupport nodes points edges weights (.vertex i) := by
  rw [weightQuery, ← weightAtoms_refs, supports_atomRefs,
    weightAtoms_set points _ hg.ordered (groupAt_sublist points i), atomKeys_domain]
  rfl

omit [DecidableEq ι] in
theorem tableSpec_congr {K : Type*} (support support' : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) (ht : TableSpec support keys nodes table)
    (he : ∀ k ∈ keys, support k = support' k) : TableSpec support' keys nodes table := by
  induction ht with
  | nil => exact .nil
  | @cons k entry keys table hh ht ih =>
    exact .cons ⟨hh.1, hh.2.1, hh.2.2.trans (he k (by simp))⟩
      (ih (fun k hk => he k (by simp [hk])))

/-- Both actual coarse output tables represent precisely the partition cells
of the original weighted graph, including all persistent-node invariants. -/
theorem coarse_cell_specs {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    Valid cw.1 ∧ Extends nodes cw.1 ∧
      TableSpec (fun p => coarseSupport nodes points edges weights (.edge p.1 p.2))
        (pairs (List.range groups.length)) cw.1 ce.2 ∧
      TableSpec (fun i => coarseSupport nodes points edges weights (.vertex i))
        (List.range groups.length) cw.1 cw.2 := by
  have hh := coarse_builds hg
  exact ⟨hh.1, hh.2.1, tableSpec_congr _ _ _ _ _ hh.2.2.1 (edgeQuery_support hg),
    tableSpec_congr _ _ _ _ _ hh.2.2.2 (fun i _ => weightQuery_support hg i)⟩

/-- Disjoint coarse source cells inherit disjoint original input payloads. -/
theorem coarseSupport_disjointOn {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    SupportInterpretation.DisjointOn (coarseSupport nodes points edges weights)
      (PairedCoarseSupport.atomDomain (List.range (PairGrouping.groups points).length)) := by
  have hw := atomSupport_disjointOn hg
  rw [atomKeys_domain] at hw
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  exact SupportInterpretation.disjointOn_blocks _ _ _ _ hw
    (PairedCoarseSupport.cells_disjointOn _ points hn (PairedCoarseSupport.domain_within points hg.ordered))
    (fun c _ => PairedCoarseSupport.cell_subset _ points c)

/-- The actual completed coarse graph satisfies the full recursive input
invariant: canonical keys, sorted vertices, valid disjoint references and DAG. -/
theorem coarseGraph_ready {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    GraphReady cw.1 (List.range groups.length) ce.2 cw.2 := by
  have hh := coarse_cell_specs hg
  apply graphReady_of_atomTable _ _ _ _ (coarseSupport nodes points edges weights)
    hh.1 List.pairwise_lt_range hh.2.2.1 hh.2.2.2
  intro a ha b hb hne
  apply coarseSupport_disjointOn hg _ _ hne
  · rw [← atomKeys_domain]
    exact List.mem_toFinset.mpr ha
  · rw [← atomKeys_domain]
    exact List.mem_toFinset.mpr hb

/-- The real coarse lookup references expand to exactly their original fine
source cells, so the recursive correctness theorem can be interpreted back. -/
theorem coarse_atomRef {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (c : Source ℕ)
    (hc : c ∈ PairedCoarseSupport.atomDomain (List.range (PairGrouping.groups points).length)) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    RefSpec (coarseSupport nodes points edges weights c) cw.1 (atomRef ce.2 cw.2 c) := by
  have hh := coarse_cell_specs hg
  have ht := tableSpec_atomTable _ _ _ _ _ hh.2.2.1 hh.2.2.2
  apply tableSpec_lookup _ _ _ _ ht c
  exact List.mem_toFinset.mp (by rwa [atomKeys_domain])

end IntegerMultBounds.Networks.PairedCoarseCorrect
