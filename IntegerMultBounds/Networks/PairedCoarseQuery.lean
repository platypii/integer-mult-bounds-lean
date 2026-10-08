import IntegerMultBounds.Networks.PairedQuerySupport

/-! Transport actual recursive coarse outputs back to the original fine graph.
The contraction uses genuine weighted source cells and keeps interpretation at
the current persistent DAG state, ready for the reconstruction constructors. -/

namespace IntegerMultBounds.Networks.PairedCoarseQuery

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedPartition PairedCoarseCorrect SupportInterpretation

variable {ι : Type*} [DecidableEq ι]

/-- Finite support expansion composes by literal union of the inner cells. -/
theorem interpret_comp {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (weight : B → Finset C) (cells : A → Finset B) (atoms : Finset A) :
    interpret (fun a => interpret weight (cells a)) atoms =
      interpret weight (interpret cells atoms) := by
  ext x
  simp only [mem_interpret]
  aesop

/-- Querying the actual coarse tables excludes exactly the corresponding fine
vertex groups, interpreted using the original input graph's real references. -/
theorem coarse_query_support {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (excluded : List ℕ) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    supports cw.1 (query ce.2 cw.2 excluded) =
      interpret (atomSupport nodes edges weights)
        (avoiding (atomKeys points).toFinset
          (excluded.toFinset.biUnion (PairedCoarseSupport.groupSet points))) := by
  dsimp only
  rw [PairedQuerySupport.query_support (coarseGraph_ready hg)]
  simp only [atomKeys_domain]
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  calc
    _ = interpret (coarseSupport nodes points edges weights)
        (avoiding (PairedCoarseSupport.atomDomain (List.range (PairGrouping.groups points).length))
          excluded.toFinset) := by
      apply congr_weights
      intro c hc
      exact (coarse_atomRef hg c (mem_avoiding _ _ _ |>.mp hc).1).2
    _ = _ := by
      change interpret (fun c => interpret (atomSupport nodes edges weights)
        (PairedCoarseSupport.cell (PairedCoarseSupport.atomDomain points) points c)) _ = _
      rw [interpret_comp, PairedCoarseSupport.interpret_avoiding _ points hn
        (PairedCoarseSupport.domain_within points hg.ordered)]

/-- The same coarse query has unchanged fine-source interpretation at any
later persistent state, including the state returned by the recursive call. -/
theorem coarse_query_support_at {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (he : Extends nodes larger) (excluded : List ℕ) :
    let groups := PairGrouping.groups points
    let ce := coarseEdges nodes groups edges
    let cw := coarseWeights ce.1 groups edges weights
    supports cw.1 (query ce.2 cw.2 excluded) =
      interpret (atomSupport larger edges weights)
        (avoiding (atomKeys points).toFinset
          (excluded.toFinset.biUnion (PairedCoarseSupport.groupSet points))) := by
  dsimp only
  rw [coarse_query_support hg, PairedQuerySupport.interpret_extends hg he _
    (PairedQuerySupport.avoiding_subset _ _)]

/-- The complete coarse result, now specified in terms of current fine graph
payloads. Its one/two tables remain keyed by their original coarse vertices. -/
structure RecursiveCorrect (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (result : BlockResult ι) : Prop where
  valid : Valid result.nodes
  extension : Extends nodes result.nodes
  input : GraphReady result.nodes points edges weights
  total : RefSpec (supports result.nodes (query edges weights [])) result.nodes result.total
  one_keys : List.Perm (result.one.map Prod.fst) (List.range (PairGrouping.groups points).length)
  two_keys : List.Perm (result.two.map Prod.fst) (pairs (List.range (PairGrouping.groups points).length))
  outside : ∀ i, i < (PairGrouping.groups points).length →
    RefSpec (interpret (atomSupport result.nodes edges weights)
      (avoiding (atomKeys points).toFinset (PairedCoarseSupport.groupSet points i)))
      result.nodes (lookup result.one i)
  far : ∀ p ∈ pairs (List.range (PairGrouping.groups points).length),
    RefSpec (interpret (atomSupport result.nodes edges weights)
      (avoiding (atomKeys points).toFinset
        (PairedCoarseSupport.groupSet points p.1 ∪ PairedCoarseSupport.groupSet points p.2)))
      result.nodes (lookup result.two p)

/-- Actual recursive correctness supplies all fine-graph outside/far references
needed by the upstream reconstruction, without changing any node or lookup. -/
theorem recursive_correct {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (result : BlockResult ι)
    (hc : let groups := PairGrouping.groups points
      let ce := coarseEdges nodes groups edges
      let cw := coarseWeights ce.1 groups edges weights
      BlockCorrect cw.1 (List.range groups.length) ce.2 cw.2 result) :
    RecursiveCorrect nodes points edges weights result := by
  have he := extends_trans (coarse_cell_specs hg).2.1 hc.extension
  have hi := graphReady_extends he hc.valid hg
  refine ⟨hc.valid, he, hi, ?_, hc.one_keys, hc.two_keys, ?_, ?_⟩
  · have ht := hc.total
    rw [coarse_query_support_at hg he []] at ht
    have hq := PairedQuerySupport.query_support hi []
    simp only [List.toFinset_nil, Finset.biUnion_empty] at ht hq
    rwa [← hq] at ht
  · intro i hi'
    have hh := hc.one i (List.mem_range.mpr hi')
    rw [coarse_query_support_at hg he [i]] at hh
    simpa only [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert, Finset.biUnion_empty,
      Finset.union_empty] using hh
  · intro p hp
    have hh := hc.two p hp
    rw [coarse_query_support_at hg he [p.1, p.2]] at hh
    simpa only [List.toFinset_cons, List.toFinset_nil, Finset.biUnion_insert, Finset.biUnion_empty,
      Finset.union_empty] using hh

end IntegerMultBounds.Networks.PairedCoarseQuery
