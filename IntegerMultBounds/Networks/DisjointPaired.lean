import IntegerMultBounds.Networks.DisjointBalanced
import Mathlib.Data.List.Sublists

/-! Weighted paired-exclusion builder foundations. The upstream small-block
branch computes all, leave-one-out, and leave-two-out weighted graph sums.
This file executes that branch using the upstream floor-half balanced totals
with left-before-right evaluation, zero elision, and support interning, and proves the complete returned list of references correct. The recursive
coarse-graph and strip reconstruction are not asserted here. -/

namespace IntegerMultBounds.Networks.DisjointPaired

open DisjointCircuit DisjointBuilder

variable {ι V A : Type*} [DecidableEq ι] [DecidableEq V]

private theorem supports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : supports larger refs = supports nodes refs := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    rw [supports, supports, refSupport_extends he (hr r (by simp))]
    rw [ih (fun s hs => hr s (by simp [hs]))]

omit [DecidableEq ι] in
private theorem refsValid_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : RefsValid larger refs :=
  fun r h => refValid_extends he (hr r h)

omit [DecidableEq ι] in
private theorem disjointRefs_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    DisjointRefs larger refs := by
  apply List.Pairwise.imp_of_mem _ hd
  intro l r hl hr' hdis
  rw [refSupport_extends he (hr l hl), refSupport_extends he (hr r hr')]
  exact hdis

/-- Sequentially build several totals in one shared DAG. Later totals may
intern supports already built for earlier queries. -/
def batch (nodes : List (Node ι)) : List (List Ref) → List (Node ι) × List Ref
  | [] => (nodes, [])
  | query :: queries =>
    let first := DisjointBalanced.total nodes query
    let rest := batch first.1 queries
    (rest.1, first.2 :: rest.2)

def budget (queries : List (List Ref)) : ℕ :=
  (queries.map (fun q => q.length - 1)).sum

structure BatchBuilt (nodes : List (Node ι)) (queries : List (List Ref))
    (result : List (Node ι) × List Ref) : Prop where
  valid : Valid result.1
  extension : Extends nodes result.1
  refsValid : RefsValid result.1 result.2
  supports_eq : result.2.map (refSupport result.1) = queries.map (supports nodes)
  length_le : result.1.length ≤ nodes.length + budget queries

/-- A whole batch is a valid extension, with ordered output support semantics
and a concrete bound on the total number of appended addition nodes. -/
theorem batch_built (nodes : List (Node ι)) (queries : List (List Ref)) (hv : Valid nodes)
    (hr : ∀ q ∈ queries, RefsValid nodes q) (hd : ∀ q ∈ queries, DisjointRefs nodes q) :
    BatchBuilt nodes queries (batch nodes queries) := by
  induction queries generalizing nodes with
  | nil => exact ⟨hv, extends_refl _, by simp [RefsValid, batch], rfl, by simp [batch, budget]⟩
  | cons q qs ih =>
    have hq := DisjointBalanced.total_built nodes q hv (hr q (by simp)) (hd q (by simp))
    have hrest := ih (DisjointBalanced.total nodes q).1 hq.valid
      (fun s hs => refsValid_extends hq.extension s (hr s (by simp [hs])))
      (fun s hs => disjointRefs_extends hq.extension s (hr s (by simp [hs])) (hd s (by simp [hs])))
    refine ⟨hrest.valid, extends_trans hq.extension hrest.extension, ?_, ?_, ?_⟩
    · intro r hr'
      rcases List.mem_cons.mp hr' with rfl | hrr
      · exact refValid_extends hrest.extension hq.refValid
      · exact hrest.refsValid r hrr
    · change refSupport (batch (DisjointBalanced.total nodes q).1 qs).1 (DisjointBalanced.total nodes q).2 ::
        ((batch (DisjointBalanced.total nodes q).1 qs).2.map (refSupport (batch (DisjointBalanced.total nodes q).1 qs).1)) = _
      rw [refSupport_extends hrest.extension hq.refValid, hq.support_eq, hrest.supports_eq]
      simp only [List.map_cons]
      congr 1
      apply List.map_congr_left
      intro s hs
      exact supports_extends hq.extension s (hr s (by simp [hs]))
    · have ht := hq.length_le
      have hs := hrest.length_le
      change (batch (DisjointBalanced.total nodes q).1 qs).1.length ≤ _
      simp only [budget, List.map_cons, List.sum_cons] at hs ⊢
      omega

section Values

variable [AddCommMonoid A]

/-- The entire ordered output list evaluates to the original query sums. -/
theorem batch_values (input : ι → A) (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : ∀ q ∈ queries, RefsValid nodes q)
    (hd : ∀ q ∈ queries, DisjointRefs nodes q) :
    (batch nodes queries).2.map (refValue input (batch nodes queries).1) =
      queries.map (fun q => (q.map (refValue input nodes)).sum) := by
  have hb := batch_built nodes queries hv hr hd
  calc
    _ = ((batch nodes queries).2.map (refSupport (batch nodes queries).1)).map (supportSum input) := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro r hr'
      exact refValue_eq input _ r hb.valid (hb.refsValid r hr')
    _ = (queries.map (supports nodes)).map (supportSum input) := congrArg (List.map (supportSum input)) hb.supports_eq
    _ = _ := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro q hq
      have ht := DisjointBalanced.total_built nodes q hv (hr q hq) (hd q hq)
      have he := DisjointBalanced.total_value input nodes q hv (hr q hq) (hd q hq)
      rwa [refValue_eq input _ _ ht.valid ht.refValid, ht.support_eq] at he

theorem batch_preserves (input : ι → A) (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : ∀ q ∈ queries, RefsValid nodes q)
    (hd : ∀ q ∈ queries, DisjointRefs nodes q) (old : Ref) (ho : RefValid nodes old) :
    refValue input (batch nodes queries).1 old = refValue input nodes old := by
  have hb := batch_built nodes queries hv hr hd
  exact refValue_extends input hb.extension hv hb.valid ho

end Values

/-- Each weighted term records its incident vertices and existing DAG reference.
Vertex weights have one incident vertex and graph edges have two. -/
abbrev Entry (V : Type*) := Finset V × Ref

/-- The concrete weighted graph term list used by the paired recursion. -/
def weightedEntries (edges : List (V × V × Ref)) (weights : List (V × Ref)) : List (Entry V) :=
  edges.map (fun e => ({e.1, e.2.1}, e.2.2)) ++ weights.map (fun w => ({w.1}, w.2))

/-- Exactly the terms touching none of the omitted vertices, as in the
upstream `block` small-case filter. Zero terms remain optional references. -/
def select (entries : List (Entry V)) (excluded : Finset V) : List Ref :=
  (entries.filter (fun e => decide (Disjoint e.1 excluded))).map Prod.snd

/-- The empty omission, each singleton, and each unordered pair in list order. -/
def omissions (points : List V) : List (Finset V) :=
  ∅ :: (points.map (fun p => {p}) ++ (points.sublistsLen 2).map List.toFinset)

def baseQueries (points : List V) (entries : List (Entry V)) : List (List Ref) :=
  (omissions points).map (select entries)

/-- The actual weighted all/one/two exclusion branch. It is valid for any
finite vertex list; the optimized paired recursion uses it at size at most four. -/
def baseBlock (nodes : List (Node ι)) (points : List V)
    (edges : List (V × V × Ref)) (weights : List (V × Ref)) : List (Node ι) × List Ref :=
  batch nodes (baseQueries points (weightedEntries edges weights))

omit [DecidableEq ι] in
private theorem select_refsValid (nodes : List (Node ι)) (entries : List (Entry V))
    (hr : RefsValid nodes (entries.map Prod.snd)) (excluded : Finset V) :
    RefsValid nodes (select entries excluded) := by
  intro r h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  exact hr e.2 (List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, rfl⟩)

omit [DecidableEq ι] in
private theorem select_disjoint (nodes : List (Node ι)) (entries : List (Entry V))
    (hd : DisjointRefs nodes (entries.map Prod.snd)) (excluded : Finset V) :
    DisjointRefs nodes (select entries excluded) := by
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp hd).filter _

/-- Every output of the concrete weighted small-block builder has its exact
filtered support; all old DAG nodes survive and the construction is bounded. -/
theorem baseBlock_built (nodes : List (Node ι)) (points : List V)
    (edges : List (V × V × Ref)) (weights : List (V × Ref)) (hv : Valid nodes)
    (hr : RefsValid nodes ((weightedEntries edges weights).map Prod.snd))
    (hd : DisjointRefs nodes ((weightedEntries edges weights).map Prod.snd)) :
    BatchBuilt nodes (baseQueries points (weightedEntries edges weights)) (baseBlock nodes points edges weights) := by
  apply batch_built nodes _ hv
  · intro q hq
    obtain ⟨excluded, _, rfl⟩ := List.mem_map.mp hq
    exact select_refsValid nodes _ hr excluded
  · intro q hq
    obtain ⟨excluded, _, rfl⟩ := List.mem_map.mp hq
    exact select_disjoint nodes _ hd excluded

/-- All, single-exclusion and pair-exclusion outputs equal the actual selected
edge and vertex-weight values, in the explicit order `omissions points`. -/
theorem baseBlock_values [AddCommMonoid A] (input : ι → A) (nodes : List (Node ι)) (points : List V)
    (edges : List (V × V × Ref)) (weights : List (V × Ref)) (hv : Valid nodes)
    (hr : RefsValid nodes ((weightedEntries edges weights).map Prod.snd))
    (hd : DisjointRefs nodes ((weightedEntries edges weights).map Prod.snd)) :
    (baseBlock nodes points edges weights).2.map (refValue input (baseBlock nodes points edges weights).1) =
      (omissions points).map (fun excluded =>
        ((select (weightedEntries edges weights) excluded).map (refValue input nodes)).sum) := by
  have he := batch_values input nodes (baseQueries points (weightedEntries edges weights)) hv
    (fun q hq => by
      obtain ⟨excluded, _, rfl⟩ := List.mem_map.mp hq
      exact select_refsValid nodes _ hr excluded)
    (fun q hq => by
      obtain ⟨excluded, _, rfl⟩ := List.mem_map.mp hq
      exact select_disjoint nodes _ hd excluded)
  simpa only [baseBlock, baseQueries, List.map_map, Function.comp_def] using he

/-- The empty-omission query includes every graph term, even absent weights. -/
theorem select_empty (entries : List (Entry V)) : select entries ∅ = entries.map Prod.snd := by
  simp [select]

/-- The generic incidence filter is exactly the upstream separate edge and
vertex-weight filters. -/
theorem select_weightedEntries (edges : List (V × V × Ref)) (weights : List (V × Ref))
    (excluded : Finset V) :
    select (weightedEntries edges weights) excluded =
      (edges.filter (fun e => decide (e.1 ∉ excluded ∧ e.2.1 ∉ excluded))).map (fun e => e.2.2) ++
      (weights.filter (fun w => decide (w.1 ∉ excluded))).map Prod.snd := by
  simp [select, weightedEntries, List.filter_map, Function.comp_def,
    Finset.disjoint_insert_left, Finset.disjoint_singleton_left]

/-- There is one total, one single exclusion per point, and one double
exclusion per two-element sublist. -/
theorem omissions_length (points : List V) :
    (omissions points).length = 1 + points.length + points.length.choose 2 := by
  simp [omissions, List.length_sublistsLen]
  omega

theorem omissions_single (points : List V) (p : V) (hp : p ∈ points) :
    {p} ∈ omissions points := by
  simp [omissions, hp]

theorem omissions_pair (points : List V) (p q : V) (hpq : List.Sublist [p, q] points) :
    {p, q} ∈ omissions points := by
  have hh : [p, q] ∈ points.sublistsLen 2 := List.mem_sublistsLen.mpr ⟨hpq, rfl⟩
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨[p, q], hh, by simp⟩

end IntegerMultBounds.Networks.DisjointPaired
