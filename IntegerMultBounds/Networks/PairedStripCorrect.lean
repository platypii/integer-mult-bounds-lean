import IntegerMultBounds.Networks.PairedGraphSpec
import IntegerMultBounds.Networks.PairedVectorCorrect
import IntegerMultBounds.Networks.DisjointPaired
import Mathlib.Data.List.InsertIdx

/-! Correctness of literal strip construction: balanced group totals followed
by the actual prefix/suffix vector, preserving every original reference. -/

namespace IntegerMultBounds.Networks.PairedCircuitCorrect

open DisjointCircuit DisjointBuilder PairedCircuit

variable {ι : Type*} [DecidableEq ι]

/-- The stateful total loop is exactly the previously verified batch builder,
including allocation order and the interning state passed between calls. -/
theorem mapBuild_total_eq_batch {K : Type*} (nodes : List (Node ι))
    (keys : List K) (queries : K → List Ref) :
    mapBuild (fun ns k => DisjointBalanced.total ns (queries k)) nodes keys =
      DisjointPaired.batch nodes (keys.map queries) := by
  induction keys generalizing nodes with
  | nil => rfl
  | cons k ks ih => simp [mapBuild, DisjointPaired.batch, ih]

theorem supports_foldr (nodes : List (Node ι)) (refs : List Ref) :
    supports nodes refs = (refs.map (refSupport nodes)).foldr (· ∪ ·) ∅ := by
  induction refs with
  | nil => rfl
  | cons r rs ih => simp [supports, ih]

theorem supports_append (nodes : List (Node ι)) (left right : List Ref) :
    supports nodes (left ++ right) = supports nodes left ∪ supports nodes right := by
  induction left with
  | nil => simp [supports]
  | cons r rs ih => simp [supports, ih, Finset.union_assoc]

theorem supports_flatten (nodes : List (Node ι)) (queries : List (List Ref)) :
    supports nodes queries.flatten = (queries.map (supports nodes)).foldr (· ∪ ·) ∅ := by
  induction queries with
  | nil => rfl
  | cons q qs ih => simp [supports_append, ih]

/-- Disjointness of all original operands implies disjointness of the grouped
supports; zero operands and empty groups require no nonemptiness assumptions. -/
theorem grouped_disjoint (nodes : List (Node ι)) (queries : List (List Ref))
    (hd : DisjointRefs nodes queries.flatten) :
    List.Pairwise Disjoint (queries.map (supports nodes)) := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_flatten.mp hd).2.imp
  intro left right h
  apply Disjoint.symm
  apply DisjointExclusion.disjoint_supports
  intro l hl
  apply Disjoint.symm
  exact DisjointExclusion.disjoint_supports nodes _ right (fun r hr => h l hl r hr)

/-- All grouped totals in a batch have disjoint supports when their complete
input stream does. This is the actual precondition for the following vector. -/
theorem batch_disjoint (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : RefsValid nodes queries.flatten)
    (hd : DisjointRefs nodes queries.flatten) :
    DisjointRefs (DisjointPaired.batch nodes queries).1 (DisjointPaired.batch nodes queries).2 := by
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  apply List.pairwise_map.mp
  rw [hb.supports_eq]
  exact grouped_disjoint nodes queries hd

/-- Omitting a grouped total omits exactly that original operand group. -/
theorem batch_erase_support (nodes : List (Node ι)) (queries : List (List Ref))
    (hv : Valid nodes) (hr : RefsValid nodes queries.flatten)
    (hd : DisjointRefs nodes queries.flatten) (i : ℕ) :
    supports (DisjointPaired.batch nodes queries).1 ((DisjointPaired.batch nodes queries).2.eraseIdx i) =
      supports nodes ((queries.eraseIdx i).flatten) := by
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  rw [supports_foldr, supports_flatten, ← List.eraseIdx_map, hb.supports_eq, List.eraseIdx_map]

/-- Exact original operand groups used for a strip: remaining vertex weights,
then cross-group edges in increasing other-group order. -/
def stripQueries (groups : List (List ℕ)) (edges : EdgeTable) (weights : WeightTable)
    (ia : ℕ × ℕ) : List (List Ref) :=
  let remaining := (groupAt groups ia.1).filter (· != ia.2)
  let other := (List.range groups.length).filter (· != ia.1)
  remaining.map (lookup weights) :: other.map (fun j => crossRefs edges remaining (groupAt groups j))

/-- The executable strip really performs one batch followed by one vector;
this equality preserves the exact constructor order of the upstream script. -/
theorem buildStrip_eq (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) :
    buildStrip nodes groups edges weights ia =
      let batch := DisjointPaired.batch nodes (stripQueries groups edges weights ia)
      let vec := vectorFalse batch.1 batch.2
      (vec.nodes, ⟨ia.2, vec.total, ((List.range groups.length).filter (· != ia.1)).zip vec.one.tail⟩) := by
  simp only [buildStrip, stripQueries, DisjointPaired.batch,
    mapBuild_total_eq_batch]

/-- Looking up an indexed key of a duplicate-free zip returns that exact
position's payload, rather than an assumed association-table model. -/
theorem lookup_zip_get {K : Type*} [DecidableEq K] (keys : List K) (refs : List Ref)
    (hn : keys.Nodup) (hlen : keys.length = refs.length) (i : ℕ) (hi : i < keys.length) :
    lookup (keys.zip refs) keys[i] = refs[i]'(by omega) := by
  have hk : (keys.zip refs).map Prod.fst = keys := List.map_fst_zip (by omega)
  have hz : i < (keys.zip refs).length := by simp only [List.length_zip]; omega
  apply lookup_entry _ (by rw [hk]; exact hn)
  have hm := List.getElem_mem hz
  simpa only [List.getElem_zip] using hm

/-- Complete semantics of one literal strip, expressed in original reference
groups. The first group is the carry; outside key `j` omits group `j+1`. -/
structure StripBuilt (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ)
    (result : List (Node ι) × Strip) : Prop where
  valid : Valid result.1
  extension : Extends nodes result.1
  vertex_eq : result.2.vertex = ia.2
  total : RefSpec (supports nodes (stripQueries groups edges weights ia).flatten) result.1 result.2.total
  outside_keys : result.2.outside.map Prod.fst = (List.range groups.length).filter (· != ia.1)
  outside : ∀ i (hi : i < ((List.range groups.length).filter (· != ia.1)).length),
    RefSpec (supports nodes (((stripQueries groups edges weights ia).eraseIdx (i+1)).flatten))
      result.1 (lookup result.2.outside (((List.range groups.length).filter (· != ia.1))[i]))

/-- Literal carry construction, grouped edge totals, vector construction and
keyed omissions are all correct from the original stream's disjointness. -/
theorem buildStrip_built (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ) (hv : Valid nodes)
    (hr : RefsValid nodes (stripQueries groups edges weights ia).flatten)
    (hd : DisjointRefs nodes (stripQueries groups edges weights ia).flatten) :
    StripBuilt nodes groups edges weights ia (buildStrip nodes groups edges weights ia) := by
  let queries := stripQueries groups edges weights ia
  let other := (List.range groups.length).filter (· != ia.1)
  let batch := DisjointPaired.batch nodes queries
  have hb := DisjointPaired.batch_built nodes queries hv
    (fun q hq r hr' => hr r (List.mem_flatten.mpr ⟨q, hq, hr'⟩))
    (List.pairwise_flatten.mp hd).1
  have hdis := batch_disjoint nodes queries hv hr hd
  let vec := vectorFalse batch.1 batch.2
  have hvec := PairedVectorCorrect.vectorFalse_built batch.1 batch.2 hb.valid hb.refsValid hdis
  have hblen : batch.2.length = queries.length := by
    have hh := congrArg List.length hb.supports_eq
    simpa only [List.length_map] using hh
  have hqlen : queries.length = other.length + 1 := by simp [queries, stripQueries, other]
  have hvlen : vec.one.length = other.length + 1 := by
    rw [vectorFalse_length, hblen, hqlen]
  have htlen : other.length = vec.one.tail.length := by simp only [List.length_tail]; omega
  rw [buildStrip_eq]
  change StripBuilt nodes groups edges weights ia (vec.nodes, ⟨ia.2, vec.total, other.zip vec.one.tail⟩)
  refine ⟨hvec.valid, extends_trans hb.extension hvec.extension, rfl, ?_,
    List.map_fst_zip (by omega), ?_⟩
  · refine ⟨hvec.total_valid, ?_⟩
    rw [hvec.total_support, supports_foldr, hb.supports_eq, ← supports_flatten]
  · intro i hi
    have hin : i < other.length := hi
    have hvt : i < vec.one.tail.length := by omega
    have hvi : i + 1 < vec.one.length := by omega
    have hvb : i + 1 < batch.2.length := by omega
    have he : lookup (other.zip vec.one.tail) other[i] = vec.one[i+1] := by
      rw [lookup_zip_get other vec.one.tail (List.nodup_range.filter _) htlen i hin,
        List.getElem_tail hvt]
    change RefSpec _ vec.nodes (lookup (other.zip vec.one.tail) other[i])
    rw [he]
    refine ⟨hvec.one_valid _ (List.getElem_mem hvi), ?_⟩
    have hs := PairedVectorCorrect.vectorFalse_support batch.1 batch.2 hb.valid hb.refsValid hdis (i+1) hvb
    change refSupport vec.nodes (vec.one[i+1]?.getD none) = _ at hs
    simp only [List.getElem?_eq_getElem hvi, Option.getD_some] at hs
    exact hs.trans (batch_erase_support nodes queries hv hr hd (i+1))

/-- Persistent semantic portion of a strip contract, anchored in the original
input graph and valid after later strips extend the shared DAG. -/
def StripSemantics (original : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ)
    (nodes : List (Node ι)) (out : Strip) : Prop :=
  out.vertex = ia.2 ∧
  RefSpec (supports original (stripQueries groups edges weights ia).flatten) nodes out.total ∧
  out.outside.map Prod.fst = (List.range groups.length).filter (· != ia.1) ∧
  ∀ i (hi : i < ((List.range groups.length).filter (· != ia.1)).length),
    RefSpec (supports original (((stripQueries groups edges weights ia).eraseIdx (i+1)).flatten))
      nodes (lookup out.outside (((List.range groups.length).filter (· != ia.1))[i]))

theorem stripSemantics_extends (original : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (ia : ℕ × ℕ)
    {nodes larger : List (Node ι)} (out : Strip) (he : Extends nodes larger)
    (hs : StripSemantics original groups edges weights ia nodes out) :
    StripSemantics original groups edges weights ia larger out :=
  ⟨hs.1, refSpec_extends he hs.2.1, hs.2.2.1,
    fun i hi => refSpec_extends he (hs.2.2.2 i hi)⟩

/-- The entire literal strip loop is a valid DAG extension, with every returned
strip specified in the common original-state interpretation. -/
theorem buildStrips_built (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (hv : Valid nodes)
    (hr : ∀ ia ∈ members groups, RefsValid nodes (stripQueries groups edges weights ia).flatten)
    (hd : ∀ ia ∈ members groups, DisjointRefs nodes (stripQueries groups edges weights ia).flatten) :
    let out := buildStrips nodes groups edges weights
    Valid out.1 ∧ Extends nodes out.1 ∧
      List.Forall₂ (fun ia s => StripSemantics nodes groups edges weights ia out.1 s)
        (members groups) out.2 := by
  let Inv := fun ns => Valid ns ∧ Extends nodes ns
  have hb := mapBuild_correct (fun ns ia => buildStrip ns groups edges weights ia)
    Inv (StripSemantics nodes groups edges weights)
    (fun ia ns larger out he hs => stripSemantics_extends nodes groups edges weights ia out he hs)
    nodes (members groups) ⟨hv, extends_refl _⟩ (by
      intro ns hn ia hia
      have hs := buildStrip_built ns groups edges weights ia hn.1
        (DisjointExclusion.refsValid_extends hn.2 (hr ia hia))
        (DisjointExclusion.disjointRefs_extends hn.2 _ (hr ia hia) (hd ia hia))
      refine ⟨⟨hs.valid, extends_trans hn.2 hs.extension⟩, hs.extension,
        hs.vertex_eq, ?_, hs.outside_keys, ?_⟩
      · have ht := hs.total
        rw [DisjointExclusion.supports_extends hn.2 _ (hr ia hia)] at ht
        exact ht
      · intro i hi
        have ht := hs.outside i hi
        have hr' : RefsValid nodes (((stripQueries groups edges weights ia).eraseIdx (i+1)).flatten) := by
          intro r hmem
          obtain ⟨q, hq, hqr⟩ := List.mem_flatten.mp hmem
          exact hr ia hia r (List.mem_flatten.mpr
            ⟨q, (List.eraseIdx_sublist _ _).subset hq, hqr⟩)
        rw [DisjointExclusion.supports_extends hn.2 _ hr'] at ht
        exact ht)
  exact ⟨hb.invariant.1, hb.extension, hb.outputs⟩

/-- Actual strip lookup retrieves the specified member's semantics from the
literal loop output; uniqueness is required only for the vertex keys. -/
theorem stripLookup_semantics (original : List (Node ι)) (groups : List (List ℕ))
    (edges : EdgeTable) (weights : WeightTable) (nodes : List (Node ι))
    (ias : List (ℕ × ℕ)) (strips : List Strip)
    (hs : List.Forall₂ (fun ia s => StripSemantics original groups edges weights ia nodes s) ias strips)
    (hn : (ias.map Prod.snd).Nodup) (ia : ℕ × ℕ) (hia : ia ∈ ias) :
    StripSemantics original groups edges weights ia nodes (stripLookup strips ia.2) := by
  induction hs with
  | nil => simp at hia
  | @cons key entry keys entries hh ht ih =>
    obtain ⟨hne, htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hia with rfl | hia
    · simpa [stripLookup, hh.1] using hh
    · have hkey : key.2 ≠ ia.2 := by
        intro he
        apply hne
        rw [he]
        exact List.mem_map.mpr ⟨ia, hia, rfl⟩
      simpa [stripLookup, hh.1, hkey] using ih htail hia

end IntegerMultBounds.Networks.PairedCircuitCorrect
