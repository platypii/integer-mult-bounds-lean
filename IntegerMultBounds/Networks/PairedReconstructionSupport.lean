import IntegerMultBounds.Networks.PairedCircuitCorrect
import IntegerMultBounds.Networks.PairedQuerySupport
import IntegerMultBounds.Networks.PairedStripSupport

/-! Source-level contracts discharge the real reconstruction loops' local
support-disjointness requirements. -/

namespace IntegerMultBounds.Networks.PairedReconstructionSupport

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedPartition PairedCoarseCorrect PairedQuerySupport SupportInterpretation

variable {ι : Type*} [DecidableEq ι]

def groupSet (points : List ℕ) (i : ℕ) : Finset ℕ :=
  (groupAt (PairGrouping.groups points) i).toFinset

theorem groupAt_mem (points : List ℕ) (i : ℕ) (hi : i < (PairGrouping.groups points).length) :
    groupAt (PairGrouping.groups points) i ∈ PairGrouping.groups points := by
  simp [groupAt, List.getElem?_eq_getElem hi]

theorem groupSet_card (points : List ℕ) (i : ℕ) (hi : i < (PairGrouping.groups points).length) :
    (groupSet points i).card ≤ 2 :=
  (List.toFinset_card_le _).trans (PairGrouping.group_length_le points _ (groupAt_mem points i hi))

theorem groupAt_disjoint (points : List ℕ) (hn : points.Nodup) (i j : ℕ)
    (hi : i < (PairGrouping.groups points).length) (hj : j < (PairGrouping.groups points).length)
    (hne : i ≠ j) : (groupAt (PairGrouping.groups points) i).Disjoint (groupAt (PairGrouping.groups points) j) := by
  simp only [groupAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) i j hi hj hlt
  · exact (List.pairwise_iff_getElem.mp (PairGrouping.groups_disjoint points hn) j i hj hi hgt).symm

theorem filter_toFinset_erase (xs : List ℕ) (a : ℕ) :
    (xs.filter (· != a)).toFinset = xs.toFinset.erase a := by
  ext x
  simp [and_comm]

/-- The actual inner-loop crossing query is valid and disjoint, and its exact
support is the interpreted surviving-edge bridge. -/
theorem crossQuery_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (i j a b : ℕ) (hi : i < (PairGrouping.groups points).length)
    (hj : j < (PairGrouping.groups points).length) (hne : i ≠ j) :
    RefsValid nodes (crossQuery (PairGrouping.groups points) edges (i,j) a b) ∧
    DisjointRefs nodes (crossQuery (PairGrouping.groups points) edges (i,j) a b) ∧
    supports nodes (crossQuery (PairGrouping.groups points) edges (i,j) a b) =
      interpret (atomSupport nodes edges weights)
        (bridge (atomKeys points).toFinset ((groupSet points i).erase a) ((groupSet points j).erase b)) := by
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hd := groupAt_disjoint points hn i j hi hj hne
  have hl : List.Sublist ((groupAt (PairGrouping.groups points) i).filter (· != a)) points :=
    List.filter_sublist.trans (groupAt_sublist points i)
  have hr : List.Sublist ((groupAt (PairGrouping.groups points) j).filter (· != b)) points :=
    List.filter_sublist.trans (groupAt_sublist points j)
  have hdf : ((groupAt (PairGrouping.groups points) i).filter (· != a)).Disjoint
      ((groupAt (PairGrouping.groups points) j).filter (· != b)) := by
    intro x hx hy
    exact hd (List.mem_filter.mp hx).1 (List.mem_filter.mp hy).1
  have hready := crossRefs_ready hg _ _ hl hr hdf
  refine ⟨hready.1, hready.2, ?_⟩
  change supports nodes (crossRefs edges _ _) = _
  rw [crossRefs_support hg _ _ hl.subset hr.subset hdf,
    filter_toFinset_erase, filter_toFinset_erase]
  rfl

/-- Stored strips at a given DAG carry their exact interpreted source sets. -/
structure StripsSource (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (strips : List Strip) : Prop where
  total : ∀ i, i < (PairGrouping.groups points).length → ∀ a ∈ groupAt (PairGrouping.groups points) i,
    RefSpec (interpret (atomSupport nodes edges weights)
      (strip (atomKeys points).toFinset points.toFinset (groupSet points i) a ∅))
      nodes (stripLookup strips a).total
  outside : ∀ i, i < (PairGrouping.groups points).length → ∀ a ∈ groupAt (PairGrouping.groups points) i,
    ∀ j, j < (PairGrouping.groups points).length → i ≠ j →
    RefSpec (interpret (atomSupport nodes edges weights)
      (strip (atomKeys points).toFinset points.toFinset (groupSet points i) a (groupSet points j)))
      nodes (lookup (stripLookup strips a).outside j)

/-- Source-correct coarse pair sums and strips imply the precise local
preconditions of the actual shared-left cross constructor. -/
theorem crossLeftReady_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (far : EdgeTable) (strips : List Strip) (hs : StripsSource nodes points edges weights strips)
    (hf : ∀ ij ∈ pairs (List.range (PairGrouping.groups points).length),
      RefSpec (interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points ij.1 ∪ groupSet points ij.2)))
        nodes (lookup far ij))
    (ij : ℕ × ℕ) (hij : ij ∈ pairs (List.range (PairGrouping.groups points).length))
    (a : ℕ) (ha : a ∈ groupAt (PairGrouping.groups points) ij.1) :
    CrossLeftReady nodes (PairGrouping.groups points) edges far strips ij a := by
  have hij' := (pairs_mem _ List.pairwise_lt_range ij.1 ij.2).mp hij
  have hi : ij.1 < (PairGrouping.groups points).length := List.mem_range.mp hij'.1
  have hj : ij.2 < (PairGrouping.groups points).length := List.mem_range.mp hij'.2.1
  have hne : ij.1 ≠ ij.2 := Nat.ne_of_lt hij'.2.2
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hd : Disjoint (groupSet points ij.1) (groupSet points ij.2) :=
    List.disjoint_toFinset_iff_disjoint.mpr (groupAt_disjoint points hn ij.1 ij.2 hi hj hne)
  have hfar := hf ij hij
  have hleft := hs.outside ij.1 hi a ha ij.2 hj hne
  have hwd := PairedQuerySupport.atomSupport_disjointOn hg
  have hparts (b : ℕ) := pair_disjoint_interpret (atomSupport nodes edges weights) (atomKeys points).toFinset
    points.toFinset (groupSet points ij.1) (groupSet points ij.2) a b hwd hd
  refine ⟨hg.valid, hfar.1, hleft.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfar.2, hleft.2]
    exact (hparts 0).1
  · intro b hb
    exact (crossQuery_source hg ij.1 ij.2 a b hi hj hne).1
  · intro b hb
    exact (crossQuery_source hg ij.1 ij.2 a b hi hj hne).2.1
  · intro b hb
    exact (hs.outside ij.2 hj b hb ij.1 hi (Ne.symm hne)).1
  · intro b hb
    rw [(hs.outside ij.2 hj b hb ij.1 hi (Ne.symm hne)).2,
      (crossQuery_source hg ij.1 ij.2 a b hi hj hne).2.2]
    exact (hparts b).2.1
  · intro b hb
    rw [hfar.2, hleft.2, (hs.outside ij.2 hj b hb ij.1 hi (Ne.symm hne)).2,
      (crossQuery_source hg ij.1 ij.2 a b hi hj hne).2.2]
    exact (hparts b).2.2

/-- Stored strip values retain their source interpretation throughout later
single-output and cross-pair constructor passes. -/
theorem StripsSource.extends {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} {strips : List Strip}
    (hg : GraphReady nodes points edges weights) (he : Extends nodes larger)
    (hs : StripsSource nodes points edges weights strips) :
    StripsSource larger points edges weights strips := by
  constructor
  · intro i hi a ha
    rw [interpret_extends hg he _ (strip_subset _ _ _ _ _)]
    exact refSpec_extends he (hs.total i hi a ha)
  · intro i hi a ha j hj hne
    rw [interpret_extends hg he _ (strip_subset _ _ _ _ _)]
    exact refSpec_extends he (hs.outside i hi a ha j hj hne)

/-- The real pair-reconstruction support is exactly the original filtered
query support, after weighting the genuine four source classes. -/
theorem crossPairSupport_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (far : EdgeTable) (strips : List Strip) (hs : StripsSource nodes points edges weights strips)
    (hf : ∀ ij ∈ pairs (List.range (PairGrouping.groups points).length),
      RefSpec (interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points ij.1 ∪ groupSet points ij.2)))
        nodes (lookup far ij))
    (ij : ℕ × ℕ) (hij : ij ∈ pairs (List.range (PairGrouping.groups points).length))
    (a : ℕ) (ha : a ∈ groupAt (PairGrouping.groups points) ij.1)
    (b : ℕ) (hb : b ∈ groupAt (PairGrouping.groups points) ij.2) :
    crossPairSupport nodes (PairGrouping.groups points) edges far strips ij a b =
      supports nodes (query edges weights [a,b]) := by
  have hij' := (pairs_mem _ List.pairwise_lt_range ij.1 ij.2).mp hij
  have hi : ij.1 < (PairGrouping.groups points).length := List.mem_range.mp hij'.1
  have hj : ij.2 < (PairGrouping.groups points).length := List.mem_range.mp hij'.2.1
  have hne : ij.1 ≠ ij.2 := Nat.ne_of_lt hij'.2.2
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hd : Disjoint (groupSet points ij.1) (groupSet points ij.2) :=
    List.disjoint_toFinset_iff_disjoint.mpr (groupAt_disjoint points hn ij.1 ij.2 hi hj hne)
  rw [crossPairSupport, (hf ij hij).2, (hs.outside ij.1 hi a ha ij.2 hj hne).2,
    (hs.outside ij.2 hj b hb ij.1 hi (Ne.symm hne)).2,
    (crossQuery_source hg ij.1 ij.2 a b hi hj hne).2.2,
    ← interpret_union, ← interpret_union, ← interpret_union, query_support hg]
  have he := pair_union (atomKeys points).toFinset points.toFinset (groupSet points ij.1)
    (groupSet points ij.2) a b (atomKeys_within points hg.ordered) (atomKeys_loopless points hg.ordered)
    hd (groupSet_card points ij.1 hi) (groupSet_card points ij.2 hj)
    (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.union_assoc]
    using congrArg (interpret (atomSupport nodes edges weights)) he.symm

/-- The complete actual cross-pair constructor returns every fine pair's
original omission sum when fed source-correct coarse sums and strips. -/
theorem buildCrossPairs_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (far : EdgeTable) (strips : List Strip) (hs : StripsSource nodes points edges weights strips)
    (hf : ∀ ij ∈ pairs (List.range (PairGrouping.groups points).length),
      RefSpec (interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points ij.1 ∪ groupSet points ij.2)))
        nodes (lookup far ij)) :
    let out := buildCrossPairs nodes (PairGrouping.groups points) edges far strips
    Valid out.1 ∧ Extends nodes out.1 ∧
      TableSpec (fun p => supports nodes (query edges weights [p.1,p.2]))
        ((pairs (List.range (PairGrouping.groups points).length)).flatMap
          (crossGroupKeys (PairGrouping.groups points))) out.1 out.2 :=
  buildCrossPairs_correct nodes (PairGrouping.groups points) edges far strips
    (fun p => supports nodes (query edges weights [p.1,p.2])) hg.valid
    (fun ij hij a ha => crossLeftReady_source hg far strips hs hf ij hij a ha)
    (fun ij hij a ha b hb => crossPairSupport_source hg far strips hs hf ij hij a ha b hb)

theorem mem_members (groups : List (List ℕ)) (ia : ℕ × ℕ) :
    ia ∈ members groups ↔ ia.1 < groups.length ∧ ia.2 ∈ groupAt groups ia.1 := by
  rcases ia with ⟨i,a⟩
  simp [members]

omit [DecidableEq ι] in
theorem forall₂_imp_of_mem {X Y : Type*} {R S : X → Y → Prop} {xs : List X} {ys : List Y}
    (h : List.Forall₂ R xs ys) (hs : ∀ x ∈ xs, ∀ y, R x y → S x y) : List.Forall₂ S xs ys := by
  induction h with
  | nil => exact .nil
  | @cons x y xs ys h ht ih =>
    exact .cons (hs x (by simp) y h) (ih (fun x hx y hh => hs x (by simp [hx]) y hh))

/-- Weighted source reconstruction for the complete actual singles loop. -/
theorem buildSingles_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (outside : WeightTable) (strips : List Strip) (hs : StripsSource nodes points edges weights strips)
    (ho : ∀ i, i < (PairGrouping.groups points).length →
      RefSpec (interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points i))) nodes (lookup outside i)) :
    let out := buildSingles nodes (PairGrouping.groups points) outside strips
    Valid out.1 ∧ Extends nodes out.1 ∧
      TableSpec (fun a => supports nodes (query edges weights [a]))
        ((members (PairGrouping.groups points)).map Prod.snd) out.1 out.2 := by
  have hr (ia : ℕ × ℕ) (hia : ia ∈ members (PairGrouping.groups points)) :=
    (mem_members _ ia).mp hia
  have hb := buildSingles_correct nodes (PairGrouping.groups points) outside strips hg.valid
    (fun ia hia => ⟨(ho ia.1 (hr ia hia).1).1, (hs.total ia.1 (hr ia hia).1 ia.2 (hr ia hia).2).1⟩)
    (by
      intro ia hia
      rw [(ho ia.1 (hr ia hia).1).2, (hs.total ia.1 (hr ia hia).1 ia.2 (hr ia hia).2).2]
      exact single_disjoint_interpret _ _ _ _ _ (PairedQuerySupport.atomSupport_disjointOn hg))
  refine ⟨hb.1, hb.2.1, List.forall₂_map_left_iff.mpr ?_⟩
  apply forall₂_imp_of_mem hb.2.2
  intro ia hia entry he
  refine ⟨he.1, ?_⟩
  have heq : refSupport nodes (lookup outside ia.1) ∪ refSupport nodes (stripLookup strips ia.2).total =
      supports nodes (query edges weights [ia.2]) := by
    rw [(ho ia.1 (hr ia hia).1).2, (hs.total ia.1 (hr ia hia).1 ia.2 (hr ia hia).2).2,
      ← interpret_union, query_support hg]
    have hh := single_union (atomKeys points).toFinset points.toFinset (groupSet points ia.1) ia.2
      (atomKeys_within points hg.ordered) (atomKeys_loopless points hg.ordered)
      (groupSet_card points ia.1 (hr ia hia).1) (List.mem_toFinset.mpr (hr ia hia).2)
    simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
      using congrArg (interpret (atomSupport nodes edges weights)) hh.symm
  have ht := he.2
  rw [heq] at ht
  exact ht

omit [DecidableEq ι] in
theorem tableSpec_of_mem {K : Type*} (support : K → Finset ι) (nodes : List (Node ι))
    (table : List (K × Ref)) (h : ∀ entry ∈ table, RefSpec (support entry.1) nodes entry.2) :
    TableSpec support (table.map Prod.fst) nodes table := by
  induction table with
  | nil => exact .nil
  | cons entry entries ih =>
    exact .cons ⟨rfl, h entry (by simp)⟩ (ih (fun e he => h e (by simp [he])))

/-- Within-group pair outputs are the actual reused coarse outside reference;
the paired group size proves it excludes precisely those two vertices. -/
theorem internalPairs_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (outside : WeightTable)
    (ho : ∀ i, i < (PairGrouping.groups points).length →
      RefSpec (interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points i))) nodes (lookup outside i)) :
    TableSpec (fun p => supports nodes (query edges weights [p.1,p.2]))
      ((internalPairs (PairGrouping.groups points) outside).map Prod.fst) nodes
      (internalPairs (PairGrouping.groups points) outside) := by
  apply tableSpec_of_mem
  intro entry hentry
  obtain ⟨i, hi, hentry⟩ := List.mem_flatMap.mp hentry
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hentry
  have hi' : i < (PairGrouping.groups points).length := List.mem_range.mp hi
  have hm := (pairs_mem _ (hg.ordered.sublist (groupAt_sublist points i)) p.1 p.2).mp hp
  have he := same_group (atomKeys points).toFinset (groupSet points i) p.1 p.2
    (groupSet_card points i hi') (List.mem_toFinset.mpr hm.1) (List.mem_toFinset.mpr hm.2.1)
    (Nat.ne_of_lt hm.2.2)
  change RefSpec (supports nodes (query edges weights [p.1,p.2])) nodes (lookup outside i)
  rw [query_support hg]
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, he] using ho i hi'

/-- Full strip construction supplies actual keyed source-correct references.
The operand validity and exact source identities are derived from GraphReady. -/
theorem buildStrips_source {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (hkeys : ((members (PairGrouping.groups points)).map Prod.snd).Nodup) :
    let out := buildStrips nodes (PairGrouping.groups points) edges weights
    Valid out.1 ∧ Extends nodes out.1 ∧ StripsSource out.1 points edges weights out.2 := by
  have hb := buildStrips_built nodes (PairGrouping.groups points) edges weights hg.valid
    (fun ia _ => (PairedStripSupport.stripQueries_ready hg ia).1)
    (fun ia _ => (PairedStripSupport.stripQueries_ready hg ia).2)
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · intro i hi a ha
    have hia : (i,a) ∈ members (PairGrouping.groups points) := (mem_members _ _).mpr ⟨hi,ha⟩
    have hh := stripLookup_semantics nodes (PairGrouping.groups points) edges weights _ _ _ hb.2.2 hkeys (i,a) hia
    have ht := hh.2.1
    rw [PairedStripSupport.stripQueries_support nodes points hg.ordered edges weights (i,a)] at ht
    rw [interpret_extends hg hb.2.1 _ (strip_subset _ _ _ _ _)]
    exact ht
  · intro i hi a ha j hj hne
    have hia : (i,a) ∈ members (PairGrouping.groups points) := (mem_members _ _).mpr ⟨hi,ha⟩
    have hh := stripLookup_semantics nodes (PairGrouping.groups points) edges weights _ _ _ hb.2.2 hkeys (i,a) hia
    have hjm : j ∈ ((List.range (PairGrouping.groups points).length).filter (· != i)) := by
      simp [hj, Ne.symm hne]
    obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.mp hjm
    have ht := hh.2.2.2 k hk
    rw [PairedStripSupport.stripQueries_erase_support nodes points hg.ordered edges weights (i,a) k hk] at ht
    change RefSpec (interpret (atomSupport nodes edges weights)
      (strip (atomKeys points).toFinset points.toFinset (groupSet points i) a
        (groupSet points (((List.range (PairGrouping.groups points).length).filter (· != i))[k]))))
      _ (lookup (stripLookup _ a).outside (((List.range (PairGrouping.groups points).length).filter (· != i))[k])) at ht
    rw [hkj] at ht
    rw [interpret_extends hg hb.2.1 _ (strip_subset _ _ _ _ _)]
    exact ht

end IntegerMultBounds.Networks.PairedReconstructionSupport
