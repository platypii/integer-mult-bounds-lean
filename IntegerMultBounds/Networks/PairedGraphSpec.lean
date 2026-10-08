import IntegerMultBounds.Networks.PairedCircuit
import IntegerMultBounds.Networks.PairedPartition
import IntegerMultBounds.Networks.DisjointExclusion

/-! Correctness infrastructure for the literal weighted paired-exclusion
recursion. Stateful constructor loops retain the actual DAG, reference order,
and source supports. -/

namespace IntegerMultBounds.Networks.PairedCircuitCorrect

open DisjointCircuit DisjointBuilder PairedCircuit

variable {ι X Y : Type*} [DecidableEq ι]

/-- A constructor loop preserves a state invariant, extends the actual DAG,
and proves each result's semantic predicate at the final state. -/
structure MapBuilt (nodes : List (Node ι)) (xs : List X)
    (result : List (Node ι) × List Y) (Inv : List (Node ι) → Prop)
    (Post : X → List (Node ι) → Y → Prop) : Prop where
  invariant : Inv result.1
  extension : Extends nodes result.1
  outputs : List.Forall₂ (fun x y => Post x result.1 y) xs result.2

omit [DecidableEq ι] in
theorem mapBuild_correct (f : List (Node ι) → X → List (Node ι) × Y)
    (Inv : List (Node ι) → Prop) (Post : X → List (Node ι) → Y → Prop)
    (stable : ∀ x ns larger y, Extends ns larger → Post x ns y → Post x larger y)
    (nodes : List (Node ι)) (xs : List X) (hn : Inv nodes)
    (step : ∀ ns, Inv ns → ∀ x ∈ xs,
      Inv (f ns x).1 ∧ Extends ns (f ns x).1 ∧ Post x (f ns x).1 (f ns x).2) :
    MapBuilt nodes xs (mapBuild f nodes xs) Inv Post := by
  induction xs generalizing nodes with
  | nil => exact ⟨hn, extends_refl _, .nil⟩
  | cons x xs ih =>
    obtain ⟨hfirst, he, hp⟩ := step nodes hn x (by simp)
    have ht := ih (f nodes x).1 hfirst (fun ns hs y hy => step ns hs y (by simp [hy]))
    exact ⟨ht.invariant, extends_trans he ht.extension,
      .cons (stable x _ _ _ ht.extension hp) ht.outputs⟩

/-- The reference and its full support remain meaningful in every extension. -/
def RefSpec (support : Finset ι) (nodes : List (Node ι)) (ref : Ref) : Prop :=
  RefValid nodes ref ∧ refSupport nodes ref = support

omit [DecidableEq ι] in
theorem refSpec_extends {support : Finset ι} {nodes larger : List (Node ι)} {ref : Ref}
    (he : Extends nodes larger) (hr : RefSpec support nodes ref) : RefSpec support larger ref :=
  ⟨refValid_extends he hr.1, (refSupport_extends he hr.1).trans hr.2⟩

/-- A stored association table has exact keys and valid semantic references. -/
def TableSpec {K : Type*} (support : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) : Prop :=
  List.Forall₂ (fun key entry => entry.1 = key ∧ RefSpec (support key) nodes entry.2) keys table

omit [DecidableEq ι] in
theorem tableSpec_extends {K : Type*} (support : K → Finset ι) (keys : List K)
    {nodes larger : List (Node ι)} {table : List (K × Ref)}
    (he : Extends nodes larger) (ht : TableSpec support keys nodes table) :
    TableSpec support keys larger table := by
  apply List.Forall₂.imp _ ht
  intro key entry hh
  exact ⟨hh.1, refSpec_extends he hh.2⟩

omit [DecidableEq ι] in
theorem tableSpec_keys {K : Type*} (support : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) (ht : TableSpec support keys nodes table) :
    table.map Prod.fst = keys := by
  induction ht with
  | nil => rfl
  | cons h hs ih => simp [h.1, ih]

omit [DecidableEq ι] in
/-- Finding a key in a semantically specified table returns its actual value;
no table lookup correctness or reference validity is assumed separately. -/
theorem tableSpec_lookup {K : Type*} [DecidableEq K] (support : K → Finset ι) (keys : List K)
    (nodes : List (Node ι)) (table : List (K × Ref)) (ht : TableSpec support keys nodes table)
    (key : K) (hk : key ∈ keys) : RefSpec (support key) nodes (lookup table key) := by
  induction ht with
  | nil => simp at hk
  | @cons k entry keys table hh ht ih =>
    by_cases hkey : k = key
    · subst key
      simpa [lookup, hh.1] using hh.2
    · have hmem : key ∈ keys := (List.mem_cons.mp hk).resolve_left (Ne.symm hkey)
      simpa [lookup, hh.1, hkey] using ih hmem

/-- Balanced totals turn an actual list of disjoint valid references into a
reference with its exact union support in a valid extension. -/
theorem total_refSpec (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    Valid (DisjointBalanced.total nodes refs).1 ∧
    Extends nodes (DisjointBalanced.total nodes refs).1 ∧
    RefSpec (supports nodes refs) (DisjointBalanced.total nodes refs).1 (DisjointBalanced.total nodes refs).2 := by
  have ht := DisjointBalanced.total_built nodes refs hv hr hd
  exact ⟨ht.valid, ht.extension, ht.refValid, ht.support_eq⟩

/-- Stateful list construction of balanced totals, retaining exact output keys
and original-state support semantics through every intervening extension. -/
theorem mapTotals_correct {K : Type*} (nodes : List (Node ι)) (keys : List K)
    (queries : K → List Ref) (hv : Valid nodes)
    (hr : ∀ k ∈ keys, RefsValid nodes (queries k))
    (hd : ∀ k ∈ keys, DisjointRefs nodes (queries k)) :
    let result := mapBuild (fun ns k =>
      let out := DisjointBalanced.total ns (queries k)
      (out.1, (k, out.2))) nodes keys
    Valid result.1 ∧ Extends nodes result.1 ∧
      TableSpec (fun k => supports nodes (queries k)) keys result.1 result.2 := by
  let Inv := fun ns => Valid ns ∧ Extends nodes ns
  let Post := fun k ns (out : K × Ref) => out.1 = k ∧ RefSpec (supports nodes (queries k)) ns out.2
  have hh := mapBuild_correct
    (fun ns k => let out := DisjointBalanced.total ns (queries k); (out.1, (k, out.2))) Inv Post
    (fun k ns larger out he hp => ⟨hp.1, refSpec_extends he hp.2⟩) nodes keys
    ⟨hv, extends_refl _⟩ (by
      intro ns hn k hk
      have ht := DisjointBalanced.total_built ns (queries k) hn.1
        (DisjointExclusion.refsValid_extends hn.2 (hr k hk))
        (DisjointExclusion.disjointRefs_extends hn.2 _ (hr k hk) (hd k hk))
      refine ⟨⟨ht.valid, extends_trans hn.2 ht.extension⟩, ht.extension, rfl, ht.refValid, ?_⟩
      exact ht.support_eq.trans (DisjointExclusion.supports_extends hn.2 _ (hr k hk)))
  exact ⟨hh.invariant.1, hh.extension, hh.outputs⟩

/-- The complete ordered reference list of a weighted input graph. -/
def graphRefs (edges : EdgeTable) (weights : WeightTable) : List Ref :=
  edges.map Prod.snd ++ weights.map Prod.snd

theorem query_sublist (edges : EdgeTable) (weights : WeightTable) (excluded : List ℕ) :
    List.Sublist (query edges weights excluded) (graphRefs edges weights) :=
  List.Sublist.append (List.Sublist.map _ (List.filter_sublist))
    (List.Sublist.map _ (List.filter_sublist))

/-- Semantic contract for a complete block result. Lookup order is free because
the literal recursion emits internal pairs before cross-group pairs. -/
structure BlockCorrect (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (result : BlockResult ι) : Prop where
  valid : Valid result.nodes
  extension : Extends nodes result.nodes
  total : RefSpec (supports nodes (query edges weights [])) result.nodes result.total
  one_keys : List.Perm (result.one.map Prod.fst) points
  two_keys : List.Perm (result.two.map Prod.fst) (pairs points)
  one : ∀ a ∈ points, RefSpec (supports nodes (query edges weights [a])) result.nodes (lookup result.one a)
  two : ∀ p ∈ pairs points, RefSpec (supports nodes (query edges weights [p.1, p.2])) result.nodes (lookup result.two p)

/-- Full correctness of the actual literal small-block branch, including all
returned table lookups and all prior DAG nodes. -/
theorem baseBlock_correct (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) (hv : Valid nodes)
    (hr : RefsValid nodes (graphRefs edges weights)) (hd : DisjointRefs nodes (graphRefs edges weights)) :
    BlockCorrect nodes points edges weights (baseBlock nodes points edges weights) := by
  have hrv (excluded : List ℕ) : RefsValid nodes (query edges weights excluded) :=
    fun r hh => hr r ((query_sublist edges weights excluded).subset hh)
  have hdv (excluded : List ℕ) : DisjointRefs nodes (query edges weights excluded) :=
    hd.sublist (query_sublist edges weights excluded)
  let total := DisjointBalanced.total nodes (query edges weights [])
  have ht := DisjointBalanced.total_built nodes (query edges weights []) hv (hrv []) (hdv [])
  let one := mapBuild (fun ns a =>
    let r := DisjointBalanced.total ns (query edges weights [a]); (r.1, (a, r.2))) total.1 points
  have hone := mapTotals_correct total.1 points (fun a => query edges weights [a]) ht.valid
    (fun a _ => DisjointExclusion.refsValid_extends ht.extension (hrv [a]))
    (fun a _ => DisjointExclusion.disjointRefs_extends ht.extension _ (hrv [a]) (hdv [a]))
  change Valid one.1 ∧ Extends total.1 one.1 ∧ _ at hone
  have heone : Extends nodes one.1 := extends_trans ht.extension hone.2.1
  let two := mapBuild (fun ns p =>
    let r := DisjointBalanced.total ns (query edges weights [p.1, p.2]); (r.1, (p, r.2))) one.1 (pairs points)
  have htwo := mapTotals_correct one.1 (pairs points) (fun p => query edges weights [p.1, p.2]) hone.1
    (fun p _ => DisjointExclusion.refsValid_extends heone (hrv [p.1, p.2]))
    (fun p _ => DisjointExclusion.disjointRefs_extends heone _ (hrv [p.1, p.2]) (hdv [p.1, p.2]))
  change Valid two.1 ∧ Extends one.1 two.1 ∧ _ at htwo
  have he : Extends nodes two.1 := extends_trans heone htwo.2.1
  refine ⟨htwo.1, he, ?_, ?_, ?_, ?_, ?_⟩
  · exact refSpec_extends (extends_trans hone.2.1 htwo.2.1) ⟨ht.refValid, ht.support_eq⟩
  · exact (tableSpec_keys _ _ _ _ hone.2.2).symm ▸ List.Perm.refl _
  · exact (tableSpec_keys _ _ _ _ htwo.2.2).symm ▸ List.Perm.refl _
  · intro a ha
    have hh := tableSpec_lookup _ _ _ _ hone.2.2 a ha
    have hs := DisjointExclusion.supports_extends ht.extension _ (hrv [a])
    rw [hs] at hh
    exact refSpec_extends htwo.2.1 hh
  · intro p hp
    have hh := tableSpec_lookup _ _ _ _ htwo.2.2 p hp
    have hs := DisjointExclusion.supports_extends heone _ (hrv [p.1, p.2])
    rw [hs] at hh
    exact hh

/-- The recursive input graph has exactly the canonical keys (in arbitrary
insertion order), with actual in-bounds, disjoint DAG references. -/
structure GraphReady (nodes : List (Node ι)) (points : List ℕ)
    (edges : EdgeTable) (weights : WeightTable) : Prop where
  valid : Valid nodes
  ordered : points.Pairwise (· < ·)
  edge_keys : List.Perm (edges.map Prod.fst) (pairs points)
  weight_keys : List.Perm (weights.map Prod.fst) points
  refsValid : RefsValid nodes (graphRefs edges weights)
  disjoint : DisjointRefs nodes (graphRefs edges weights)

omit [DecidableEq ι] in
theorem pairs_mem (points : List ℕ) (hp : points.Pairwise (· < ·)) (u v : ℕ) :
    (u, v) ∈ pairs points ↔ u ∈ points ∧ v ∈ points ∧ u < v := by
  induction points with
  | nil => simp [pairs]
  | cons a points ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hp
    rw [pairs]
    simp only [List.mem_append, List.mem_map, Prod.mk.injEq, ih ht, List.mem_cons]
    constructor
    · rintro (⟨b, hb, hab, hbv⟩ | ⟨hu, hv, huv⟩)
      · subst u; subst v
        exact ⟨Or.inl rfl, Or.inr hb, ha b hb⟩
      · exact ⟨Or.inr hu, Or.inr hv, huv⟩
    · rintro ⟨hu, hv, huv⟩
      rcases hu with rfl | hu
      · rcases hv with rfl | hv
        · omega
        · exact Or.inl ⟨v, hv, rfl, rfl⟩
      · rcases hv with rfl | hv
        · have := ha u hu; omega
        · exact Or.inr ⟨hu, hv, huv⟩

omit [DecidableEq ι] in
theorem pairs_nodup (points : List ℕ) (hp : points.Pairwise (· < ·)) : (pairs points).Nodup := by
  induction points with
  | nil => simp [pairs]
  | cons a points ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hp
    have hn : points.Nodup := ht.imp (fun h => Nat.ne_of_lt h)
    rw [pairs, List.nodup_append]
    refine ⟨hn.map (by intro x y h; exact (Prod.mk.inj h).2), ih ht, ?_⟩
    intro p hleft q hright heq
    subst q
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hleft
    have hm := (pairs_mem points ht a v).mp hright
    have := ha a hm.1
    omega

omit [DecidableEq ι] in
theorem lookup_entry {K : Type*} [DecidableEq K] (table : List (K × Ref))
    (hn : (table.map Prod.fst).Nodup) (key : K) (ref : Ref) (hm : (key, ref) ∈ table) :
    lookup table key = ref := by
  induction table with
  | nil => simp at hm
  | cons entry table ih =>
    obtain ⟨hne, htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst entry
      simp [lookup]
    · have hk : entry.1 ≠ key := by
        intro hh
        apply hne
        rw [hh]
        exact List.mem_map.mpr ⟨(key, ref), hm, rfl⟩
      simpa [lookup, hk] using ih htail hm

/-- Literal support accumulation agrees with finite union interpretation. -/
theorem supports_toFinset (nodes : List (Node ι)) (refs : List Ref) :
    supports nodes refs = refs.toFinset.biUnion (refSupport nodes) := by
  induction refs with
  | nil => simp [supports]
  | cons r rs ih => simp [supports, ih]

/-- Read-only input graph references remain a valid disjoint family throughout
any valid extension produced by a nested constructor. -/
theorem graphReady_extends {nodes larger : List (Node ι)} {points : List ℕ}
    {edges : EdgeTable} {weights : WeightTable} (he : Extends nodes larger)
    (hv : Valid larger) (hg : GraphReady nodes points edges weights) :
    GraphReady larger points edges weights :=
  ⟨hv, hg.ordered, hg.edge_keys, hg.weight_keys,
    DisjointExclusion.refsValid_extends he hg.refsValid,
    DisjointExclusion.disjointRefs_extends he _ hg.refsValid hg.disjoint⟩

/-- Support of an ordered table query is the finite union over its actual
selected keys, with each payload obtained by the executable table lookup. -/
theorem table_query_support {K : Type*} [DecidableEq K] (nodes : List (Node ι))
    (table : List (K × Ref)) (hn : (table.map Prod.fst).Nodup) (select : K → Bool) :
    supports nodes ((table.filter (fun e => select e.1)).map Prod.snd) =
      ((table.map Prod.fst).toFinset.filter (fun k => select k)).biUnion
        (fun k => refSupport nodes (lookup table k)) := by
  rw [supports_toFinset]
  ext x
  simp only [Finset.mem_biUnion, List.mem_toFinset, List.mem_map, List.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨entry, ⟨hentry, hselect⟩, rfl⟩, hx⟩
    refine ⟨entry.1, ⟨⟨entry, hentry, rfl⟩, hselect⟩, ?_⟩
    rw [lookup_entry table hn entry.1 entry.2 (by simpa using hentry)]
    exact hx
  · rintro ⟨k, ⟨⟨entry, hentry, rfl⟩, hselect⟩, hx⟩
    refine ⟨entry.2, ⟨entry, ⟨hentry, hselect⟩, rfl⟩, ?_⟩
    rwa [lookup_entry table hn entry.1 entry.2 (by simpa using hentry)] at hx

@[simp] theorem query_empty (edges : EdgeTable) (weights : WeightTable) :
    query edges weights [] = graphRefs edges weights := by simp [query, graphRefs]

/-- A complete result gives the desired actual weighted sums and preserves
all prior node values; this is derived from support correctness, not a second
independent evaluation model. -/
theorem BlockCorrect.total_value {A : Type*} [AddCommMonoid A] (input : ι → A)
    {nodes : List (Node ι)} {points : List ℕ} {edges : EdgeTable} {weights : WeightTable}
    {result : BlockResult ι} (hc : BlockCorrect nodes points edges weights result)
    (hg : GraphReady nodes points edges weights) :
    refValue input result.nodes result.total = (graphRefs edges weights |>.map (refValue input nodes)).sum := by
  rw [refValue_eq input _ _ hc.valid hc.total.1, hc.total.2, query_empty]
  have ht := DisjointBalanced.total_built nodes (graphRefs edges weights) hg.valid hg.refsValid hg.disjoint
  have hh := DisjointBalanced.total_value input nodes (graphRefs edges weights) hg.valid hg.refsValid hg.disjoint
  rwa [refValue_eq input _ _ ht.valid ht.refValid, ht.support_eq] at hh

theorem BlockCorrect.preserves {A : Type*} [AddCommMonoid A] (input : ι → A)
    {nodes : List (Node ι)} {points : List ℕ} {edges : EdgeTable} {weights : WeightTable}
    {result : BlockResult ι} (hc : BlockCorrect nodes points edges weights result)
    (hv : Valid nodes) (old : Ref) (ho : RefValid nodes old) :
    refValue input result.nodes old = refValue input nodes old :=
  refValue_extends input hc.extension hv hc.valid ho

end IntegerMultBounds.Networks.PairedCircuitCorrect
