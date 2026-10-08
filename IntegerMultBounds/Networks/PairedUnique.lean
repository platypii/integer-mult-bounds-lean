import IntegerMultBounds.Networks.DisjointUnique
import IntegerMultBounds.Networks.PairedInitialGraph

/-! Support interning remains globally unique through every literal paired
constructor and recursive level. The final nonempty-support invariant is then
derived from the already-proved validity of the actual completed DAG. -/

namespace IntegerMultBounds.Networks.PairedUnique

open DisjointCircuit DisjointBuilder DisjointUnique PairedCircuit PairedCircuitCorrect
variable {ι : Type*} [DecidableEq ι]

abbrev SupportsNodup (nodes : List (Node ι)) : Prop := (nodes.map Node.support).Nodup

omit [DecidableEq ι] in
theorem mapBuild_nodup {X Y : Type*} (f : List (Node ι) → X → List (Node ι) × Y)
    (nodes : List (Node ι)) (xs : List X) (hn : SupportsNodup nodes)
    (hf : ∀ ns x, SupportsNodup ns → SupportsNodup (f ns x).1) :
    SupportsNodup (mapBuild f nodes xs).1 := by
  induction xs generalizing nodes with
  | nil => exact hn
  | cons x xs ih => exact ih _ (hf nodes x hn)

theorem prefixBuild_nodup (nodes : List (Node ι)) (acc : Ref) (refs : List Ref)
    (hn : SupportsNodup nodes) : SupportsNodup (prefixBuild nodes acc refs).1 := by
  induction refs generalizing nodes acc with
  | nil => exact hn
  | cons r rs ih => exact ih _ _ (smartAdd_nodup nodes acc r hn)

theorem suffixBuild_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : SupportsNodup nodes) : SupportsNodup (suffixBuild nodes refs).1 := by
  induction refs with
  | nil => exact hn
  | cons r rs ih => exact smartAdd_nodup _ _ _ ih

theorem vectorFalse_nodup (nodes : List (Node ι)) (refs : List Ref)
    (hn : SupportsNodup nodes) : SupportsNodup (vectorFalse nodes refs).nodes :=
  mapBuild_nodup _ _ _ (suffixBuild_nodup _ _ (prefixBuild_nodup nodes none refs hn))
    (fun ns p hs => smartAdd_nodup ns p.1 p.2 hs)

theorem baseBlock_nodup (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hn : SupportsNodup nodes) :
    SupportsNodup (baseBlock nodes points edges weights).nodes := by
  have ht := balanced_total_nodup nodes (query edges weights []) hn
  have ho := mapBuild_nodup (fun ns a =>
    let r := DisjointBalanced.total ns (query edges weights [a]); (r.1, (a, r.2)))
    _ points ht (fun ns a hs => balanced_total_nodup ns (query edges weights [a]) hs)
  exact mapBuild_nodup _ _ _ ho
    (fun ns p hs => balanced_total_nodup ns (query edges weights [p.1, p.2]) hs)

theorem coarseEdges_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (hn : SupportsNodup nodes) : SupportsNodup (coarseEdges nodes groups edges).1 :=
  mapBuild_nodup _ _ _ hn (fun ns _p hs => balanced_total_nodup ns _ hs)

theorem coarseWeights_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hn : SupportsNodup nodes) :
    SupportsNodup (coarseWeights nodes groups edges weights).1 :=
  mapBuild_nodup _ _ _ hn (fun ns _i hs => balanced_total_nodup ns _ hs)

theorem buildStrip_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) (hn : SupportsNodup nodes) :
    SupportsNodup (buildStrip nodes groups edges weights ia).1 := by
  apply vectorFalse_nodup
  apply mapBuild_nodup
  · exact balanced_total_nodup nodes _ hn
  · intro ns i hs
    exact balanced_total_nodup ns _ hs

theorem buildStrips_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hn : SupportsNodup nodes) :
    SupportsNodup (buildStrips nodes groups edges weights).1 :=
  mapBuild_nodup _ _ _ hn (fun ns ia hs => buildStrip_nodup ns groups edges weights ia hs)

theorem buildSingles_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) (hn : SupportsNodup nodes) :
    SupportsNodup (buildSingles nodes groups outside strips).1 :=
  mapBuild_nodup _ _ _ hn (fun ns _ia hs => smartAdd_nodup ns _ _ hs)

theorem buildCrossLeft_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ)
    (hn : SupportsNodup nodes) : SupportsNodup (buildCrossLeft nodes groups edges far strips ij a).1 := by
  apply mapBuild_nodup
  · exact smartAdd_nodup nodes _ _ hn
  · intro ns b hs
    apply smartAdd_nodup
    apply smartAdd_nodup
    exact balanced_total_nodup ns _ hs

theorem buildCrossGroup_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ)
    (hn : SupportsNodup nodes) : SupportsNodup (buildCrossGroup nodes groups edges far strips ij).1 :=
  mapBuild_nodup _ _ _ hn (fun ns a hs => buildCrossLeft_nodup ns groups edges far strips ij a hs)

theorem buildCrossPairs_nodup (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (far : EdgeTable) (strips : List Strip) (hn : SupportsNodup nodes) :
    SupportsNodup (buildCrossPairs nodes groups edges far strips).1 :=
  mapBuild_nodup _ _ _ hn (fun ns ij hs => buildCrossGroup_nodup ns groups edges far strips ij hs)

theorem reconstruct_nodup (groups : List (List ℕ)) (edges : EdgeTable) (weights : WeightTable)
    (coarse : BlockResult ι) (hn : SupportsNodup coarse.nodes) :
    SupportsNodup (reconstruct groups edges weights coarse).nodes :=
  buildCrossPairs_nodup _ _ _ _ _
    (buildSingles_nodup _ _ _ _ (buildStrips_nodup _ _ _ _ hn))

/-- Uniqueness holds for the whole literal recursion and arbitrary references,
not merely a tree without sharing or a separately annotated node list. -/
theorem block_nodup (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hn : SupportsNodup nodes) :
    SupportsNodup (block nodes points edges weights).nodes := by
  induction points using (measure (fun ps : List ℕ => ps.length)).wf.induction
      generalizing nodes edges weights with
  | h points ih =>
    rw [block]
    split
    · exact baseBlock_nodup nodes points edges weights hn
    · rename_i hlarge
      let groups := PairGrouping.groups points
      have he := coarseEdges_nodup nodes groups edges hn
      have hw := coarseWeights_nodup _ groups edges weights he
      apply reconstruct_nodup
      exact ih (List.range groups.length)
        (by
          change (List.range groups.length).length < points.length
          simpa only [List.length_range] using PairGrouping.length_groups_lt points (by omega))
        _ _ _ hw

/-- Valid weighted recursion preserves pairwise-distinct nonempty supports. -/
theorem block_unique (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hg : GraphReady nodes points edges weights)
    (hn : SupportsNodup nodes) : Unique (block nodes points edges weights).nodes :=
  unique_of_valid_nodup _ (PairedBlockCorrect.block_correct nodes points edges weights hg).valid
    (block_nodup nodes points edges weights hn)

/-- Initial singleton input nodes are unique in literal pair order. -/
theorem initial_nodup (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    SupportsNodup (PairedInitialGraph.nodes points) := by
  have hn := pairs_nodup points hs
  simp only [SupportsNodup, PairedInitialGraph.nodes, List.map_map, Function.comp_def]
  exact hn.map (fun p q h => Finset.singleton_injective h)

/-- Every stored support is nonempty and no two stored nodes have equal
supports, across every level and all shared query subcomputations. -/
theorem circuit_unique (points : List ℕ) (hs : points.Pairwise (· < ·)) :
    Unique (PairedInitialGraph.circuit points).nodes :=
  block_unique _ _ _ _ (PairedInitialGraph.graphReady points hs) (initial_nodup points hs)

theorem circuit49_unique : Unique (PairedInitialGraph.circuit (List.range 49)).nodes :=
  circuit_unique _ List.pairwise_lt_range

end IntegerMultBounds.Networks.PairedUnique
