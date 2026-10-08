import IntegerMultBounds.Networks.PairedReconstructionSupport
import IntegerMultBounds.Networks.PairedCoarseQuery
import IntegerMultBounds.Networks.PairedReconstructionKeys

/-! Assembly of the literal paired recursion from the verified coarse call,
actual strip loops, and source-level reconstruction. -/

namespace IntegerMultBounds.Networks.PairedBlockCorrect

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect
open PairedPartition PairedCoarseCorrect PairedQuerySupport SupportInterpretation
open PairedReconstructionSupport

variable {ι : Type*} [DecidableEq ι]

/-- The literal reconstruction produces the complete fine-graph contract from
source-correct coarse outputs. The list identities account for the upstream's actual enumeration order. -/
theorem reconstruct_correct (points : List ℕ) (edges : EdgeTable) (weights : WeightTable)
    (coarse : BlockResult ι) (hg : GraphReady coarse.nodes points edges weights)
    (htotal : RefSpec (supports coarse.nodes (query edges weights [])) coarse.nodes coarse.total)
    (ho : ∀ i, i < (PairGrouping.groups points).length →
      RefSpec (interpret (atomSupport coarse.nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points i))) coarse.nodes (lookup coarse.one i))
    (hf : ∀ ij ∈ pairs (List.range (PairGrouping.groups points).length),
      RefSpec (interpret (atomSupport coarse.nodes edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points ij.1 ∪ groupSet points ij.2)))
        coarse.nodes (lookup coarse.two ij))
 :
    BlockCorrect coarse.nodes points edges weights
      (reconstruct (PairGrouping.groups points) edges weights coarse) := by
  have hmembers := PairedReconstructionKeys.members_groups points
  have hpairs := PairedReconstructionKeys.reconstructionKeys_perm points coarse.one
  have hn : points.Nodup := hg.ordered.imp (fun h => Nat.ne_of_lt h)
  have hkeys : ((members (PairGrouping.groups points)).map Prod.snd).Nodup := by rwa [hmembers]
  let strips := buildStrips coarse.nodes (PairGrouping.groups points) edges weights
  have hs := buildStrips_source hg hkeys
  change Valid strips.1 ∧ Extends coarse.nodes strips.1 ∧ StripsSource strips.1 points edges weights strips.2 at hs
  have houtside {larger : List (Node ι)} (he : Extends coarse.nodes larger)
      (i : ℕ) (hi : i < (PairGrouping.groups points).length) :
      RefSpec (interpret (atomSupport larger edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points i))) larger (lookup coarse.one i) := by
    rw [interpret_extends hg he _ (avoiding_subset _ _)]
    exact refSpec_extends he (ho i hi)
  have hfar {larger : List (Node ι)} (he : Extends coarse.nodes larger)
      (ij : ℕ × ℕ) (hij : ij ∈ pairs (List.range (PairGrouping.groups points).length)) :
      RefSpec (interpret (atomSupport larger edges weights)
        (avoiding (atomKeys points).toFinset (groupSet points ij.1 ∪ groupSet points ij.2)))
        larger (lookup coarse.two ij) := by
    rw [interpret_extends hg he _ (avoiding_subset _ _)]
    exact refSpec_extends he (hf ij hij)
  let single := buildSingles strips.1 (PairGrouping.groups points) coarse.one strips.2
  have hgstrips := graphReady_extends hs.2.1 hs.1 hg
  have hone := buildSingles_source hgstrips coarse.one strips.2 hs.2.2 (houtside hs.2.1)
  change Valid single.1 ∧ Extends strips.1 single.1 ∧ _ at hone
  have heone : Extends coarse.nodes single.1 := extends_trans hs.2.1 hone.2.1
  let cross := buildCrossPairs single.1 (PairGrouping.groups points) edges coarse.two strips.2
  have hcross := buildCrossPairs_source (graphReady_extends heone hone.1 hg) coarse.two strips.2
    (hs.2.2.extends hgstrips hone.2.1) (hfar heone)
  change Valid cross.1 ∧ Extends single.1 cross.1 ∧ _ at hcross
  have he : Extends coarse.nodes cross.1 := extends_trans heone hcross.2.1
  have hrv (excluded : List ℕ) : RefsValid coarse.nodes (query edges weights excluded) :=
    fun r hr => hg.refsValid r ((query_sublist edges weights excluded).subset hr)
  have honeTable := PairedCircuitCorrect.tableSpec_congr _
    (fun a => supports coarse.nodes (query edges weights [a])) _ hone.2.2
    (fun a _ => DisjointExclusion.supports_extends hs.2.1 _ (hrv [a]))
  rw [hmembers] at honeTable
  have hcrossTable := PairedCircuitCorrect.tableSpec_congr _
    (fun p => supports coarse.nodes (query edges weights [p.1,p.2])) _ hcross.2.2
    (fun p _ => DisjointExclusion.supports_extends heone _ (hrv [p.1,p.2]))
  have hinternal := tableSpec_extends _ _ he (internalPairs_source hg coarse.one ho)
  have hpairTable := tableSpec_append _ _ hinternal hcrossTable
  change BlockCorrect coarse.nodes points edges weights
    ⟨cross.1, coarse.total, single.2, internalPairs (PairGrouping.groups points) coarse.one ++ cross.2⟩
  refine ⟨hcross.1, he, refSpec_extends he htotal, ?_, ?_, ?_, ?_⟩
  · exact (tableSpec_keys _ _ _ _ honeTable) ▸ List.Perm.refl _
  · rw [List.map_append, tableSpec_keys _ _ _ _ hcrossTable]
    exact hpairs
  · intro a ha
    exact refSpec_extends hcross.2.1 (tableSpec_lookup _ _ _ _ honeTable a ha)
  · intro p hp
    exact tableSpec_lookup _ _ _ _ hpairTable p (hpairs.mem_iff.mpr hp)

/-- Change only the reference-support anchor to an earlier valid input graph;
the complete constructed DAG and executable outputs remain exactly the same. -/
theorem blockCorrect_prepend {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} {result : BlockResult ι}
    (hg : GraphReady nodes points edges weights) (he : Extends nodes larger)
    (hc : BlockCorrect larger points edges weights result) :
    BlockCorrect nodes points edges weights result := by
  have hr (excluded : List ℕ) : RefsValid nodes (query edges weights excluded) :=
    fun r hm => hg.refsValid r ((query_sublist edges weights excluded).subset hm)
  refine ⟨hc.valid, extends_trans he hc.extension, ?_, hc.one_keys, hc.two_keys, ?_, ?_⟩
  · have ht := hc.total
    rwa [DisjointExclusion.supports_extends he _ (hr [])] at ht
  · intro a ha
    have ht := hc.one a ha
    rwa [DisjointExclusion.supports_extends he _ (hr [a])] at ht
  · intro p hp
    have ht := hc.two p hp
    rwa [DisjointExclusion.supports_extends he _ (hr [p.1,p.2])] at ht

/-- Full correctness of the literal recursive upstream weighted paired-exclusion
algorithm. The structural input invariant implies validity, preservation,
all total/single/pair supports, and the exact executable association lookups.
No supplied checker result or recursive-correctness premise is assumed. -/
theorem block_correct (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights) :
    BlockCorrect nodes points edges weights (block nodes points edges weights) := by
  have main : ∀ n, ∀ (points : List ℕ), points.length = n →
      ∀ (nodes : List (Node ι)) (edges : EdgeTable) (weights : WeightTable),
      GraphReady nodes points edges weights →
      BlockCorrect nodes points edges weights (block nodes points edges weights) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro points hlen nodes edges weights hg
      by_cases hsmall : points.length ≤ 4
      · rw [block_small nodes points edges weights hsmall]
        exact baseBlock_correct nodes points edges weights hg.valid hg.refsValid hg.disjoint
      · have hlarge : 4 < points.length := by omega
        let groups := PairGrouping.groups points
        let ce := coarseEdges nodes groups edges
        let cw := coarseWeights ce.1 groups edges weights
        let coarse := block cw.1 (List.range groups.length) ce.2 cw.2
        have hclen : (List.range groups.length).length < n := by
          rw [List.length_range, ← hlen]
          exact PairGrouping.length_groups_lt points hlarge
        have hcoarse := ih (List.range groups.length).length hclen (List.range groups.length) rfl
          cw.1 ce.2 cw.2 (coarseGraph_ready hg)
        have hr := PairedCoarseQuery.recursive_correct hg coarse hcoarse
        have hfinish := reconstruct_correct points edges weights coarse hr.input hr.total hr.outside hr.far
        rw [block_large nodes points edges weights hlarge]
        exact blockCorrect_prepend hg hr.extension hfinish
  exact main points.length points rfl nodes edges weights hg

section Values
variable {A : Type*} [AddCommMonoid A]

private theorem query_value (input : ι → A) {nodes : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (excluded : List ℕ) :
    supportSum input (supports nodes (query edges weights excluded)) =
      ((query edges weights excluded).map (refValue input nodes)).sum := by
  have hr : RefsValid nodes (query edges weights excluded) :=
    fun r hm => hg.refsValid r ((query_sublist edges weights excluded).subset hm)
  have hd : DisjointRefs nodes (query edges weights excluded) :=
    hg.disjoint.sublist (query_sublist edges weights excluded)
  have ht := DisjointBalanced.total_built nodes (query edges weights excluded) hg.valid hr hd
  have hv := DisjointBalanced.total_value input nodes (query edges weights excluded) hg.valid hr hd
  rwa [refValue_eq input _ _ ht.valid ht.refValid, ht.support_eq] at hv

/-- The actual recursively constructed total evaluates to every original edge
and vertex weight, for arbitrary additive commutative values. -/
theorem block_total_value (input : ι → A) (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights) :
    refValue input (block nodes points edges weights).nodes (block nodes points edges weights).total =
      ((graphRefs edges weights).map (refValue input nodes)).sum :=
  (block_correct nodes points edges weights hg).total_value input hg

/-- Every actual single-exclusion lookup evaluates to precisely the surviving
original edge and vertex weights. -/
theorem block_one_value (input : ι → A) (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights)
    (a : ℕ) (ha : a ∈ points) :
    refValue input (block nodes points edges weights).nodes (lookup (block nodes points edges weights).one a) =
      ((query edges weights [a]).map (refValue input nodes)).sum := by
  have hc := block_correct nodes points edges weights hg
  have ho := hc.one a ha
  rw [refValue_eq input _ _ hc.valid ho.1, ho.2]
  exact query_value input hg [a]

/-- Every actual pair-exclusion lookup evaluates to precisely the surviving
original edge and vertex weights. -/
theorem block_two_value (input : ι → A) (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights)
    (p : ℕ × ℕ) (hp : p ∈ pairs points) :
    refValue input (block nodes points edges weights).nodes (lookup (block nodes points edges weights).two p) =
      ((query edges weights [p.1,p.2]).map (refValue input nodes)).sum := by
  have hc := block_correct nodes points edges weights hg
  have ho := hc.two p hp
  rw [refValue_eq input _ _ hc.valid ho.1, ho.2]
  exact query_value input hg [p.1,p.2]

/-- The full recursion preserves every previously valid DAG reference. -/
theorem block_preserves (input : ι → A) (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights)
    (old : Ref) (hold : RefValid nodes old) :
    refValue input (block nodes points edges weights).nodes old = refValue input nodes old :=
  (block_correct nodes points edges weights hg).preserves input hg.valid old hold

end Values

end IntegerMultBounds.Networks.PairedBlockCorrect
