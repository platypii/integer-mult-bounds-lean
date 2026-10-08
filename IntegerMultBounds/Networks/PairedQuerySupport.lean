import IntegerMultBounds.Networks.PairedCoarseCorrect
import IntegerMultBounds.Networks.SupportInterpretation

/-! The literal ordered table query agrees with source-set interpretation.
This connects recursive output contracts to concrete partition identities. -/

namespace IntegerMultBounds.Networks.PairedQuerySupport

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedPartition PairedCoarseCorrect SupportInterpretation

variable {ι : Type*} [DecidableEq ι]

/-- Canonical graph atoms are duplicate-free for strictly ordered vertices. -/
theorem atomKeys_nodup (points : List ℕ) (hp : points.Pairwise (· < ·)) :
    (atomKeys points).Nodup := by
  have hn : points.Nodup := hp.imp (fun h => Nat.ne_of_lt h)
  rw [atomKeys, List.nodup_append]
  refine ⟨(pairs_nodup points hp).map (fun p q h => Prod.ext (Source.edge.inj h).1 (Source.edge.inj h).2),
    hn.map (fun _ _ h => Source.vertex.inj h), ?_⟩
  intro a ha b hb hab
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
  cases hab

/-- The script's separate edge and weight filters are exactly one incidence
filter on the actual tagged table, preserving order and all zero references. -/
theorem query_atomTable (edges : EdgeTable) (weights : WeightTable) (excluded : List ℕ) :
    query edges weights excluded =
      ((atomTable edges weights).filter (fun e => decide (Disjoint (endpoints e.1) excluded.toFinset))).map Prod.snd := by
  simp [query, atomTable, List.filter_map, List.map_map, Function.comp_def,
    endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]

/-- The actual input graph's disjoint-reference invariant gives a disjoint
interpretation of all named vertex and edge atoms. -/
theorem atomSupport_disjointOn {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights) :
    DisjointOn (atomSupport nodes edges weights) (atomKeys points).toFinset := by
  intro a ha b hb hne
  exact atomSupport_disjoint hg a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hne

/-- Exact support of any actual executable omission query. No correctness of
lookup or of a hypothetical source-level algorithm is assumed. -/
theorem query_support {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (excluded : List ℕ) :
    supports nodes (query edges weights excluded) =
      interpret (atomSupport nodes edges weights) (avoiding (atomKeys points).toFinset excluded.toFinset) := by
  rw [query_atomTable]
  have hn : ((atomTable edges weights).map Prod.fst).Nodup :=
    (atomTable_keys hg).nodup_iff.mpr (atomKeys_nodup points hg.ordered)
  rw [table_query_support nodes _ hn (fun a => decide (Disjoint (endpoints a) excluded.toFinset))]
  have he : ((atomTable edges weights).map Prod.fst).toFinset = (atomKeys points).toFinset := by
    ext a
    simpa only [List.mem_toFinset] using (atomTable_keys hg).mem_iff
  rw [he]
  simp only [decide_eq_true_eq]
  rfl

/-- Each original atom's payload is invariant under any valid extension;
subsequent source interpretation always refers to the same actual inputs. -/
theorem atomSupport_extends {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (he : Extends nodes larger) (a : Source ℕ) (ha : a ∈ (atomKeys points).toFinset) :
    atomSupport larger edges weights a = atomSupport nodes edges weights a :=
  refSupport_extends he (atomRef_valid hg a (List.mem_toFinset.mp ha))

theorem interpret_extends {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (he : Extends nodes larger) (atoms : Finset (Source ℕ)) (ha : atoms ⊆ (atomKeys points).toFinset) :
    interpret (atomSupport larger edges weights) atoms = interpret (atomSupport nodes edges weights) atoms :=
  congr_weights _ _ atoms (fun a ham => atomSupport_extends hg he a (ha ham))

/-- Canonical graph atoms have only endpoints from the actual vertex list. -/
theorem atomKeys_within (points : List ℕ) (hp : points.Pairwise (· < ·)) :
    Within (atomKeys points).toFinset points.toFinset := by
  intro s hs
  cases s with
  | vertex v => simpa [endpoints] using hs
  | edge u v =>
    have hm := (pairs_mem points hp u v).mp ((edge_mem_atomKeys points u v).mp (List.mem_toFinset.mp hs))
    simpa [endpoints, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hm.1 hm.2.1

/-- The canonical edge orientation excludes self-loops. -/
theorem atomKeys_loopless (points : List ℕ) (hp : points.Pairwise (· < ·)) :
    Loopless (atomKeys points).toFinset := by
  intro u v hs
  exact Nat.ne_of_lt ((pairs_mem points hp u v).mp
    ((edge_mem_atomKeys points u v).mp (List.mem_toFinset.mp hs))).2.2

/-- Any actual cross-reference stream between disjoint vertex sublists is a
valid disjoint stream of the original graph's payload references. -/
theorem crossRefs_ready {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (left right : List ℕ) (hl : List.Sublist left points) (hr : List.Sublist right points)
    (hd : left.Disjoint right) :
    RefsValid nodes (crossRefs edges left right) ∧ DisjointRefs nodes (crossRefs edges left right) := by
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  simpa only [crossAtoms_refs] using atomRefs_ready hg (crossAtoms left right)
    (crossAtoms_subset points left right hg.ordered hl.subset hr.subset hd)
    (crossAtoms_nodup left right (hn.sublist hl) (hn.sublist hr) hd)

/-- An actual cross-reference stream interprets precisely the source bridge. -/
theorem crossRefs_support {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (left right : List ℕ) (hl : left ⊆ points) (hr : right ⊆ points) (hd : left.Disjoint right) :
    supports nodes (crossRefs edges left right) =
      interpret (atomSupport nodes edges weights) (bridge (atomKeys points).toFinset left.toFinset right.toFinset) := by
  rw [← crossAtoms_refs edges weights, supports_atomRefs, crossAtoms_set points left right hg.ordered hl hr hd]

/-- All partition components are subsets of the original finite source set. -/
theorem strip_subset (sources : Finset (Source ℕ)) (points group : Finset ℕ) (a : ℕ)
    (excluded : Finset ℕ) : strip sources points group a excluded ⊆ sources :=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem bridge_subset (sources : Finset (Source ℕ)) (left right : Finset ℕ) :
    bridge sources left right ⊆ sources := Finset.filter_subset _ _

theorem avoiding_subset (sources : Finset (Source ℕ)) (excluded : Finset ℕ) :
    avoiding sources excluded ⊆ sources := Finset.filter_subset _ _

/-- Weighted interpretations retain the single-reconstruction disjointness. -/
theorem single_disjoint_interpret (weight : Source ℕ → Finset ι) (sources : Finset (Source ℕ))
    (points group : Finset ℕ) (a : ℕ) (hd : DisjointOn weight sources) :
    Disjoint (interpret weight (avoiding sources group))
      (interpret weight (strip sources points group a ∅)) :=
  disjoint_interpret weight sources _ _ hd (avoiding_subset _ _) (strip_subset _ _ _ _ _)
    (single_disjoint sources points group a)

/-- Weighted interpretations retain the exact upstream three-addition grouping. -/
theorem pair_disjoint_interpret (weight : Source ℕ → Finset ι) (sources : Finset (Source ℕ))
    (points left right : Finset ℕ) (a b : ℕ) (hw : DisjointOn weight sources)
    (hd : Disjoint left right) :
    Disjoint (interpret weight (avoiding sources (left ∪ right)))
      (interpret weight (strip sources points left a right)) ∧
    Disjoint (interpret weight (strip sources points right b left))
      (interpret weight (bridge sources (left.erase a) (right.erase b))) ∧
    Disjoint (interpret weight (avoiding sources (left ∪ right)) ∪
        interpret weight (strip sources points left a right))
      (interpret weight (strip sources points right b left) ∪
        interpret weight (bridge sources (left.erase a) (right.erase b))) := by
  obtain ⟨h1, h2, h3⟩ := pair_script_disjoint sources points left right a b hd
  refine ⟨disjoint_interpret weight sources _ _ hw (avoiding_subset _ _) (strip_subset _ _ _ _ _) h1,
    disjoint_interpret weight sources _ _ hw (strip_subset _ _ _ _ _) (bridge_subset _ _ _) h2, ?_⟩
  rw [← interpret_union, ← interpret_union]
  exact disjoint_interpret weight sources _ _ hw
    (Finset.union_subset (avoiding_subset _ _) (strip_subset _ _ _ _ _))
    (Finset.union_subset (strip_subset _ _ _ _ _) (bridge_subset _ _ _)) h3

end IntegerMultBounds.Networks.PairedQuerySupport
