import IntegerMultBounds.Networks.PairedStripCorrect
import IntegerMultBounds.Networks.PairedCoarseCorrect
import IntegerMultBounds.Networks.PairedCoarseSupport

/-! Literal strip operands are disjoint valid references of the original
weighted graph. Their supports are interpreted as the actual strip partitions. -/

namespace IntegerMultBounds.Networks.PairedStripSupport

open DisjointCircuit DisjointBuilder PairedCircuit PairedCircuitCorrect PairedCoarseCorrect
open PairedPartition

/-- Naming the original source atoms in exactly the strip operand order. -/
def stripAtoms (groups : List (List ℕ)) (ia : ℕ × ℕ) : List (Source ℕ) :=
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  remaining.map Source.vertex ++ other.flatMap (fun j => crossAtoms remaining (groupAt groups j))

@[simp] theorem stripAtoms_refs (groups : List (List ℕ)) (edges : EdgeTable)
    (weights : WeightTable) (ia : ℕ × ℕ) :
    (stripAtoms groups ia).map (atomRef edges weights) =
      (stripQueries groups edges weights ia).flatten := by
  simp [stripAtoms, stripQueries, List.map_map, Function.comp_def, List.flatMap_def]

private theorem crossAtoms_disjoint (left right₁ right₂ : List ℕ)
    (hl : left.Disjoint right₂) (hr : right₁.Disjoint right₂) :
    (crossAtoms left right₁).Disjoint (crossAtoms left right₂) := by
  intro x hx hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, hxy⟩ := List.mem_map.mp hy
  have hp' := List.mem_product.mp hp
  have hq' := List.mem_product.mp hq
  have he := Source.edge.inj hxy.symm
  have hn : p.1 ≠ q.2 := fun h => List.disjoint_left.mp hl hp'.1 (h ▸ hq'.2)
  have he₂ : p.2 = q.2 := by change min p.1 p.2 = min q.1 q.2 ∧ max p.1 p.2 = max q.1 q.2 at he; omega
  exact List.disjoint_left.mp hr hp'.2 (he₂ ▸ hq'.2)

theorem stripAtoms_subset (points : List ℕ) (hs : points.Pairwise (· < ·)) (ia : ℕ × ℕ) :
    stripAtoms (PairGrouping.groups points) ia ⊆ atomKeys points := by
  have hn := hs.imp (fun h => Nat.ne_of_lt h)
  intro atom ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact (vertex_mem_atomKeys points v).mpr ((groupAt_sublist points ia.1).subset (List.mem_filter.mp hv).1)
  · obtain ⟨j, hj, ha⟩ := List.mem_flatMap.mp ha
    have hji : j ≠ ia.1 := by simpa using (List.mem_filter.mp hj).2
    apply crossAtoms_subset points _ _ hs _ (groupAt_sublist points j).subset _ ha
    · intro v hv
      exact (groupAt_sublist points ia.1).subset (List.mem_filter.mp hv).1
    · intro x hx hy
      exact groupAt_disjoint points hn ia.1 j hji.symm (List.mem_filter.mp hx).1 hy

theorem stripAtoms_nodup (points : List ℕ) (hn : points.Nodup) (ia : ℕ × ℕ) :
    (stripAtoms (PairGrouping.groups points) ia).Nodup := by
  let groups := PairGrouping.groups points
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  have hrem : remaining.Nodup := ((groupAt_sublist points ia.1).nodup hn).filter _
  have hdis (j : ℕ) (hj : j ∈ other) : remaining.Disjoint (groupAt groups j) := by
    have hji : j ≠ ia.1 := by simpa [other] using (List.mem_filter.mp hj).2
    intro x hx hy
    exact groupAt_disjoint points hn ia.1 j hji.symm (List.mem_filter.mp hx).1 hy
  change (remaining.map Source.vertex ++ other.flatMap (fun j => crossAtoms remaining (groupAt groups j))).Nodup
  rw [List.nodup_append]
  refine ⟨hrem.map (fun _ _ h => Source.vertex.inj h), ?_, ?_⟩
  · rw [List.nodup_flatMap]
    constructor
    · intro j hj
      exact crossAtoms_nodup _ _ hrem ((groupAt_sublist points j).nodup hn) (hdis j hj)
    · apply List.Pairwise.imp_of_mem _ (List.nodup_range.filter (fun j => j != ia.1))
      intro i j hi hj hij
      exact crossAtoms_disjoint _ _ _ (hdis j hj) (groupAt_disjoint points hn i j hij)
  · intro x hx y hy he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    cases he

/-- The input graph invariant discharges every operand premise of the actual
strip constructor; no disjointness is assumed at the strip call site. -/
theorem stripQueries_ready {nodes : List (Node ι)} [DecidableEq ι] {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (hg : GraphReady nodes points edges weights)
    (ia : ℕ × ℕ) :
    RefsValid nodes (stripQueries (PairGrouping.groups points) edges weights ia).flatten ∧
    DisjointRefs nodes (stripQueries (PairGrouping.groups points) edges weights ia).flatten := by
  have hh := atomRefs_ready hg (stripAtoms (PairGrouping.groups points) ia)
    (stripAtoms_subset points hg.ordered ia)
    (stripAtoms_nodup points (hg.ordered.imp (fun h => Nat.ne_of_lt h)) ia)
  simpa only [stripAtoms_refs] using hh

/-- Source atoms of a strip after retaining an arbitrary list of other groups. -/
def selectedAtoms (groups : List (List ℕ)) (ia : ℕ × ℕ) (js : List ℕ) : List (Source ℕ) :=
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  remaining.map Source.vertex ++ js.flatMap (fun j => crossAtoms remaining (groupAt groups j))

private theorem bridge_union_right (sources : Finset (Source ℕ)) (left r₁ r₂ : Finset ℕ) :
    bridge sources left (r₁ ∪ r₂) = bridge sources left r₁ ∪ bridge sources left r₂ := by
  ext a
  cases a <;> simp only [bridge, Finset.mem_filter, Finset.mem_union, decide_eq_true_eq]
  all_goals aesop

private theorem vertices_set (points remaining : List ℕ) (hr : remaining ⊆ points) :
    (remaining.map Source.vertex).toFinset = vertexWeights (atomKeys points).toFinset remaining.toFinset := by
  ext a
  cases a with
  | vertex v => simp [vertexWeights]; exact fun h => hr h
  | edge u v => simp [vertexWeights]

/-- Exact source partition of the selected strips, before expanding weighted
atoms into their original DAG input supports. -/
theorem selectedAtoms_set (points : List ℕ) (hs : points.Pairwise (· < ·))
    (ia : ℕ × ℕ) (js : List ℕ) (hj : ∀ j ∈ js, j ≠ ia.1) :
    (selectedAtoms (PairGrouping.groups points) ia js).toFinset =
      vertexWeights (atomKeys points).toFinset
        ((groupAt (PairGrouping.groups points) ia.1).toFinset.erase ia.2) ∪
      bridge (atomKeys points).toFinset
        ((groupAt (PairGrouping.groups points) ia.1).toFinset.erase ia.2)
        (js.toFinset.biUnion (fun j => (groupAt (PairGrouping.groups points) j).toFinset)) := by
  let groups := PairGrouping.groups points
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  have hr : remaining ⊆ points := fun _ h => (groupAt_sublist points ia.1).subset (List.mem_filter.mp h).1
  have hn := hs.imp (fun h => Nat.ne_of_lt h)
  have he : remaining.toFinset = (groupAt groups ia.1).toFinset.erase ia.2 := by
    ext v; simp [remaining, and_comm]
  have hd (j : ℕ) (h : j ≠ ia.1) : remaining.Disjoint (groupAt groups j) := by
    intro v hv hjv
    exact groupAt_disjoint points hn ia.1 j h.symm (List.mem_filter.mp hv).1 hjv
  have hc : (js.flatMap (fun j => crossAtoms remaining (groupAt groups j))).toFinset =
      bridge (atomKeys points).toFinset remaining.toFinset
        (js.toFinset.biUnion (fun j => (groupAt groups j).toFinset)) := by
    induction js with
    | nil => ext a; cases a <;> simp [bridge]
    | cons j js ih =>
      simp only [List.flatMap_cons, List.toFinset_append, List.toFinset_cons, Finset.biUnion_insert]
      rw [crossAtoms_set points remaining (groupAt groups j) hs hr (groupAt_sublist points j).subset
        (hd j (hj j (by simp))), ih (fun k hk => hj k (by simp [hk])), bridge_union_right]
  change (remaining.map Source.vertex ++ js.flatMap _).toFinset = _
  rw [List.toFinset_append, vertices_set points remaining hr, hc, he]

open PairedCoarseSupport SupportInterpretation

/-- Selecting exactly the nonexcluded group indices selects precisely the
fine vertices outside the excluded groups. -/
theorem selected_groups_union (points : List ℕ) (hn : points.Nodup)
    (js : List ℕ) (excluded : Finset ℕ)
    (hjs : ∀ j, j ∈ js ↔ j < (PairGrouping.groups points).length ∧ j ∉ excluded) :
    js.toFinset.biUnion (groupSet points) =
      points.toFinset \ excluded.biUnion (groupSet points) := by
  ext v
  simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_sdiff]
  constructor
  · rintro ⟨j, hj, hv⟩
    have hvp : v ∈ points := (groupAt_sublist points j).subset (List.mem_toFinset.mp hv)
    refine ⟨hvp, ?_⟩
    rintro ⟨k, hk, hvk⟩
    have he : j = k := ((mem_group_iff points hn v j hvp).mp hv).symm.trans
      ((mem_group_iff points hn v k hvp).mp hvk)
    exact (hjs j).mp hj |>.2 (he ▸ hk)
  · rintro ⟨hvp, he⟩
    have hl := location_spec points v hvp
    refine ⟨location points v, (hjs _).mpr ⟨hl.1, ?_⟩, hl.2⟩
    intro hm
    exact he ⟨location points v, hm, hl.2⟩

/-- A selected strip is the actual fine-source strip with those extra coarse
groups omitted. This includes both the full strip and every keyed omission. -/
theorem selectedAtoms_strip (points : List ℕ) (hs : points.Pairwise (· < ·))
    (ia : ℕ × ℕ) (js : List ℕ) (excluded : Finset ℕ)
    (hjs : ∀ j, j ∈ js ↔ j < (PairGrouping.groups points).length ∧ j ≠ ia.1 ∧ j ∉ excluded) :
    (selectedAtoms (PairGrouping.groups points) ia js).toFinset =
      strip (atomKeys points).toFinset points.toFinset (groupSet points ia.1) ia.2
        (excluded.biUnion (groupSet points)) := by
  rw [selectedAtoms_set points hs ia js (fun j hj => ((hjs j).mp hj).2.1)]
  have hu := selected_groups_union points (hs.imp (fun h => Nat.ne_of_lt h)) js (insert ia.1 excluded)
    (by intro j; simpa [and_assoc] using hjs j)
  change _ ∪ bridge _ _ (js.toFinset.biUnion (groupSet points)) = _
  rw [hu, Finset.biUnion_insert]
  have hd : points.toFinset \ (groupSet points ia.1 ∪ excluded.biUnion (groupSet points)) =
      (points.toFinset \ groupSet points ia.1) \ excluded.biUnion (groupSet points) := by
    ext v; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
  rw [hd]
  rfl

/-- Full strip support expressed in actual original DAG inputs. -/
theorem stripQueries_support (nodes : List (Node ι)) [DecidableEq ι] (points : List ℕ)
    (hs : points.Pairwise (· < ·)) (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    supports nodes (stripQueries (PairGrouping.groups points) edges weights ia).flatten =
      interpret (atomSupport nodes edges weights)
        (strip (atomKeys points).toFinset points.toFinset (groupSet points ia.1) ia.2 ∅) := by
  rw [← stripAtoms_refs, supports_atomRefs]
  have hh := selectedAtoms_strip points hs ia
    ((List.range (PairGrouping.groups points).length).filter (· != ia.1)) ∅
    (by intro j; simp)
  simpa only [stripAtoms, selectedAtoms, Finset.biUnion_empty] using
    congrArg (interpret (atomSupport nodes edges weights)) hh

private theorem mem_eraseIdx_nodup (xs : List ℕ) (hn : xs.Nodup) (i : ℕ) (hi : i < xs.length)
    (v : ℕ) : v ∈ xs.eraseIdx i ↔ v ∈ xs ∧ v ≠ xs[i] := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j, hj, hne, rfl⟩
    exact ⟨List.getElem_mem hj, fun h => hne (hn.getElem_inj_iff.mp h)⟩
  · rintro ⟨hv, hne⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    exact ⟨j, hj, fun h => hne (by subst j; rfl), rfl⟩

/-- Omitting one literal grouped operand gives the strip outside exactly
that operand's coarse group, retaining the original vertex carry. -/
theorem stripQueries_erase_support (nodes : List (Node ι)) [DecidableEq ι] (points : List ℕ)
    (hs : points.Pairwise (· < ·)) (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ)
    (i : ℕ) (hi : i < ((List.range (PairGrouping.groups points).length).filter (· != ia.1)).length) :
    supports nodes (((stripQueries (PairGrouping.groups points) edges weights ia).eraseIdx (i+1)).flatten) =
      interpret (atomSupport nodes edges weights)
        (strip (atomKeys points).toFinset points.toFinset (groupSet points ia.1) ia.2
          (groupSet points (((List.range (PairGrouping.groups points).length).filter (· != ia.1))[i]))) := by
  let other := (List.range (PairGrouping.groups points).length).filter (· != ia.1)
  have he : (((stripQueries (PairGrouping.groups points) edges weights ia).eraseIdx (i+1)).flatten) =
      (selectedAtoms (PairGrouping.groups points) ia (other.eraseIdx i)).map (atomRef edges weights) := by
    simp [stripQueries, selectedAtoms, other, List.eraseIdx_map, List.flatMap_def,
      List.map_map, Function.comp_def]
  rw [he, supports_atomRefs]
  have hh := selectedAtoms_strip points hs ia (other.eraseIdx i) {other[i]}
    (by
      intro j
      rw [mem_eraseIdx_nodup other (List.nodup_range.filter _) i hi j]
      simp [other, and_assoc])
  simpa [other] using congrArg (interpret (atomSupport nodes edges weights)) hh

end IntegerMultBounds.Networks.PairedStripSupport
