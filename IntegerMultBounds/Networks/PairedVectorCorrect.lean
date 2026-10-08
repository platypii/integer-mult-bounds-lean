import IntegerMultBounds.Networks.PairedCircuit
import IntegerMultBounds.Networks.DisjointExclusion

/-! Correctness of the literal prefix-then-suffix vector branch used by the
paired recursion. The results describe its actual persistent DAG and every
returned reference, including the total and each ordered omission. -/

namespace IntegerMultBounds.Networks.PairedVectorCorrect

open DisjointCircuit DisjointBuilder PairedCircuit DisjointExclusion
variable {ι : Type*} [DecidableEq ι]

/-- The support before every prefix position, including the final total. -/
def beforeSupports (nodes : List (Node ι)) (acc : Finset ι) : List Ref → List (Finset ι)
  | [] => [acc]
  | r :: rs => acc :: beforeSupports nodes (acc ∪ refSupport nodes r) rs

theorem beforeSupports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (acc : Finset ι) :
    beforeSupports larger acc refs = beforeSupports nodes acc refs := by
  induction refs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    simp only [beforeSupports, refSupport_extends he (hr r (by simp))]
    rw [ih (fun r h => hr r (by simp [h]))]

theorem prefixBuild_built (nodes : List (Node ι)) (acc : Ref) (refs : List Ref)
    (hv : Valid nodes) (hp : RefValid nodes acc) (hr : RefsValid nodes refs)
    (hd : DisjointRefs nodes (acc :: refs)) :
    BatchBuilt nodes (prefixBuild nodes acc refs)
      (beforeSupports nodes (refSupport nodes acc) refs) refs.length := by
  induction refs generalizing nodes acc with
  | nil =>
    exact ⟨hv, extends_refl _, by simpa [prefixBuild, RefsValid] using hp, rfl, by simp [prefixBuild]⟩
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : RefsValid nodes rs := fun x hx => hr x (by simp [hx])
    have hdp := List.pairwise_cons.mp hd
    have hdr := List.pairwise_cons.mp hdp.2
    have ha := smartAdd_built nodes acc r hv hp hr0 (hdp.1 r (by simp))
    have hnew : DisjointRefs (smartAdd nodes acc r).1 ((smartAdd nodes acc r).2 :: rs) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, disjointRefs_extends ha.extension rs hrs hdr.2⟩
      intro x hx
      rw [ha.support_eq, refSupport_extends ha.extension (hrs x hx)]
      exact Finset.disjoint_union_left.mpr ⟨hdp.1 x (by simp [hx]), hdr.1 x hx⟩
    have hi := ih _ _ ha.valid ha.refValid (refsValid_extends ha.extension hrs) hnew
    refine ⟨hi.valid, extends_trans ha.extension hi.extension, ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ acc :: (prefixBuild _ _ rs).2 at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact refValid_extends (extends_trans ha.extension hi.extension) hp
      · exact hi.refs_valid x hx
    · change refSupport (prefixBuild _ _ rs).1 acc ::
        (prefixBuild _ _ rs).2.map (refSupport (prefixBuild _ _ rs).1) = _
      rw [refSupport_extends (extends_trans ha.extension hi.extension) hp, hi.supports_eq,
        ha.support_eq, beforeSupports_extends ha.extension rs hrs]
      rfl
    · have h1 := ha.length_le
      have h2 := hi.length_le
      change (prefixBuild _ _ rs).1.length ≤ nodes.length + (r :: rs).length
      simp only [List.length_cons]
      omega

/-- The suffix pass is definitionally the earlier verified suffix constructor,
with its total prepended to its list of strict-after references. -/
theorem suffixBuild_eq (nodes : List (Node ι)) (refs : List Ref) :
    suffixBuild nodes refs = ((suffixes nodes refs).nodes,
      (suffixes nodes refs).total :: (suffixes nodes refs).after) := by
  induction refs with
  | nil => rfl
  | cons r rs ih => simp [suffixBuild, suffixes, ih]

private theorem beforeSupports_ne_nil (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref) :
    beforeSupports nodes acc refs ≠ [] := by cases refs <;> simp [beforeSupports]

theorem beforeSupports_last (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref) :
    (beforeSupports nodes acc refs).getLast?.getD ∅ = acc ∪ supports nodes refs := by
  induction refs generalizing acc with
  | nil => simp [beforeSupports, supports]
  | cons r rs ih =>
    rw [beforeSupports, List.getLast?_cons_of_ne_nil (beforeSupports_ne_nil nodes _ rs), ih]
    simp [supports, Finset.union_assoc]

omit [DecidableEq ι] in
private theorem refSupport_last (nodes : List (Node ι)) (rs : List Ref) :
    refSupport nodes (rs.getLast?.getD none) = (rs.map (refSupport nodes)).getLast?.getD ∅ := by
  rw [List.getLast?_map]
  cases rs.getLast? <;> rfl

omit [DecidableEq ι] in
private theorem refValid_last (nodes : List (Node ι)) (rs : List Ref) (hr : RefsValid nodes rs) :
    RefValid nodes (rs.getLast?.getD none) := by
  cases h : rs.getLast? with
  | none => trivial
  | some r => exact hr r (List.mem_of_getLast? h)

/-- Independent disjoint pairs may share operands across queries; the builder
threads all additions through one persistent, support-interning DAG. -/
theorem addPairs_built (nodes : List (Node ι)) (ps : List (Ref × Ref)) (hv : Valid nodes)
    (hr : ∀ p ∈ ps, RefValid nodes p.1 ∧ RefValid nodes p.2)
    (hd : ∀ p ∈ ps, Disjoint (refSupport nodes p.1) (refSupport nodes p.2)) :
    BatchBuilt nodes (mapBuild (fun ns p => smartAdd ns p.1 p.2) nodes ps)
      (ps.map (fun p => refSupport nodes p.1 ∪ refSupport nodes p.2)) ps.length := by
  induction ps generalizing nodes with
  | nil => exact ⟨hv, extends_refl _, by simp [mapBuild, RefsValid], rfl, by simp [mapBuild]⟩
  | cons p ps ih =>
    have hp := hr p (by simp)
    have ha := smartAdd_built nodes p.1 p.2 hv hp.1 hp.2 (hd p (by simp))
    have hi := ih _ ha.valid
      (fun q hq => ⟨refValid_extends ha.extension (hr q (by simp [hq])).1,
        refValid_extends ha.extension (hr q (by simp [hq])).2⟩)
      (fun q hq => by
        rw [refSupport_extends ha.extension (hr q (by simp [hq])).1,
          refSupport_extends ha.extension (hr q (by simp [hq])).2]
        exact hd q (by simp [hq]))
    refine ⟨hi.valid, extends_trans ha.extension hi.extension, ?_, ?_, ?_⟩
    · intro r hr'
      change r ∈ (smartAdd nodes p.1 p.2).2 :: (mapBuild _ _ ps).2 at hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact refValid_extends hi.extension ha.refValid
      · exact hi.refs_valid r hr'
    · change refSupport (mapBuild _ _ ps).1 (smartAdd nodes p.1 p.2).2 ::
        (mapBuild _ _ ps).2.map (refSupport (mapBuild _ _ ps).1) = _
      rw [refSupport_extends hi.extension ha.refValid, ha.support_eq, hi.supports_eq]
      simp only [List.map_cons]
      congr 1
      apply List.map_congr_left
      intro q hq
      rw [refSupport_extends ha.extension (hr q (by simp [hq])).1,
        refSupport_extends ha.extension (hr q (by simp [hq])).2]
    · have h1 := ha.length_le
      have h2 := hi.length_le
      change (mapBuild _ _ ps).1.length ≤ nodes.length + (p :: ps).length
      simp only [List.length_cons]
      omega

/-- Prefix and strict-suffix support pairs have the intended omission unions. -/
theorem zip_supports (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref) :
    ((beforeSupports nodes acc refs).zip (afterSupports nodes refs)).map
      (fun p => p.1 ∪ p.2) = omitSupports nodes acc refs := by
  induction refs generalizing acc with
  | nil => rfl
  | cons r rs ih => simp [beforeSupports, afterSupports, omitSupports, ih]

/-- Every actual omission combines disjoint prefix and strict-suffix supports. -/
theorem zip_disjoint (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref)
    (ha : ∀ r ∈ refs, Disjoint acc (refSupport nodes r)) (hd : DisjointRefs nodes refs) :
    ∀ p ∈ (beforeSupports nodes acc refs).zip (afterSupports nodes refs), Disjoint p.1 p.2 := by
  induction refs generalizing acc with
  | nil => simp [afterSupports]
  | cons r rs ih =>
    have hh := List.pairwise_cons.mp hd
    intro p hp
    simp only [beforeSupports, afterSupports, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact disjoint_supports nodes acc rs (fun r hr => ha r (by simp [hr]))
    · exact ih (acc ∪ refSupport nodes r)
        (fun s hs => Finset.disjoint_union_left.mpr ⟨ha s (by simp [hs]), hh.1 s hs⟩) hh.2 p hp

private theorem afterSupports_length (nodes : List (Node ι)) (refs : List Ref) :
    (afterSupports nodes refs).length = refs.length := by
  induction refs with
  | nil => rfl
  | cons r rs ih => simp [afterSupports, ih]

structure VectorBuilt (nodes : List (Node ι)) (refs : List Ref) (result : VectorResult ι) : Prop where
  valid : Valid result.nodes
  extension : Extends nodes result.nodes
  total_valid : RefValid result.nodes result.total
  total_support : refSupport result.nodes result.total = supports nodes refs
  one_valid : RefsValid result.nodes result.one
  one_supports : result.one.map (refSupport result.nodes) = omitSupports nodes ∅ refs
  length_le : result.nodes.length ≤ nodes.length + 3 * refs.length

/-- The literal three-pass constructor produces the exact total and every
omission, with a persistent valid DAG and at most three new nodes per input. -/
theorem vectorFalse_built (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    VectorBuilt nodes refs (vectorFalse nodes refs) := by
  let pre := prefixBuild nodes none refs
  have hp := prefixBuild_built nodes none refs hv trivial hr
    (List.pairwise_cons.mpr ⟨by simp [refSupport], hd⟩)
  let suf := suffixes pre.1 refs
  have hs := suffixes_built pre.1 refs hp.valid (refsValid_extends hp.extension hr)
    (disjointRefs_extends hp.extension refs hr hd)
  have hpre : pre.2.map (refSupport suf.nodes) = beforeSupports nodes ∅ refs := by
    rw [map_refSupport_extends hs.built.extension pre.2 hp.refs_valid, hp.supports_eq]
    rfl
  have hsuf : suf.after.map (refSupport suf.nodes) = afterSupports nodes refs := by
    rw [hs.after_supports, afterSupports_extends hp.extension refs hr]
  let ps := pre.2.zip suf.after
  have hps : ps.map (Prod.map (refSupport suf.nodes) (refSupport suf.nodes)) =
      (beforeSupports nodes ∅ refs).zip (afterSupports nodes refs) := by
    rw [← List.zip_map, hpre, hsuf]
  have hvalid : ∀ p ∈ ps, RefValid suf.nodes p.1 ∧ RefValid suf.nodes p.2 := by
    intro p h
    have hh := List.of_mem_zip h
    exact ⟨refValid_extends hs.built.extension (hp.refs_valid p.1 hh.1), hs.after_valid p.2 hh.2⟩
  have hdis : ∀ p ∈ ps, Disjoint (refSupport suf.nodes p.1) (refSupport suf.nodes p.2) := by
    intro p h
    have hm : Prod.map (refSupport suf.nodes) (refSupport suf.nodes) p ∈
        (beforeSupports nodes ∅ refs).zip (afterSupports nodes refs) := by
      rw [← hps]
      exact List.mem_map.mpr ⟨p, h, rfl⟩
    exact zip_disjoint nodes ∅ refs (by simp) hd _ hm
  have ho := addPairs_built suf.nodes ps hs.built.valid hvalid hdis
  let outs := mapBuild (fun ns p => smartAdd ns p.1 p.2) suf.nodes ps
  have he : vectorFalse nodes refs = ⟨outs.1, pre.2.getLast?.getD none, outs.2⟩ := by
    simp only [vectorFalse, suffixBuild_eq, List.tail_cons]
    rfl
  rw [he]
  have hlvalid := refValid_last pre.1 pre.2 hp.refs_valid
  refine ⟨ho.valid, extends_trans hp.extension (extends_trans hs.built.extension ho.extension),
    refValid_extends (extends_trans hs.built.extension ho.extension) hlvalid, ?_, ho.refs_valid, ?_, ?_⟩
  · change refSupport outs.1 (pre.2.getLast?.getD none) = _
    rw [refSupport_extends (extends_trans hs.built.extension ho.extension) hlvalid,
      refSupport_last, hp.supports_eq, beforeSupports_last]
    exact Finset.empty_union _
  · change outs.2.map (refSupport outs.1) = _
    rw [ho.supports_eq]
    have heq := congrArg (List.map (fun p : Finset ι × Finset ι => p.1 ∪ p.2)) hps
    simp only [List.map_map, Function.comp_def, Prod.map] at heq
    rw [heq, zip_supports]
  · have h1 := hp.length_le
    have h2 := hs.built.length_le
    have h3 := ho.length_le
    have hplen : ps.length ≤ refs.length := by
      have hlen := congrArg List.length hps
      simp only [List.length_map, List.length_zip, afterSupports_length] at hlen
      rw [hlen]
      exact Nat.min_le_right _ _
    change outs.1.length ≤ _
    dsimp only [pre, suf, outs] at h1 h2 h3 ⊢
    omega

/-- Every returned output reference has the exact support excluding its
corresponding input position. None references count as genuine empty operands. -/
theorem vectorFalse_support (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (i : ℕ) (hi : i < refs.length) :
    refSupport (vectorFalse nodes refs).nodes ((vectorFalse nodes refs).one[i]?.getD none) =
      supports nodes (refs.eraseIdx i) := by
  have hb := vectorFalse_built nodes refs hv hr hd
  have hout : i < (vectorFalse nodes refs).one.length := by rw [vectorFalse_length nodes refs]; exact hi
  have he := congrArg (fun xs : List (Finset ι) => xs[i]?) hb.one_supports
  rw [List.getElem?_map, List.getElem?_eq_getElem hout, Option.map_some,
    omitSupports_getElem? nodes ∅ refs i hi, Finset.empty_union] at he
  simp only [List.getElem?_eq_getElem hout, Option.getD_some]
  exact Option.some.inj he

section Values
variable {A : Type*} [AddCommMonoid A]

private theorem supportSum_eq_values (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    supportSum input (supports nodes refs) = (refs.map (refValue input nodes)).sum := by
  have ht := total_built nodes refs hv hr hd
  have he := total_value input nodes refs hv hr hd
  rw [refValue_eq input _ _ ht.valid ht.refValid, ht.support_eq] at he
  exact he

/-- The returned total evaluates to the sum of the original operand values. -/
theorem vectorFalse_total_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    refValue input (vectorFalse nodes refs).nodes (vectorFalse nodes refs).total =
      (refs.map (refValue input nodes)).sum := by
  have hb := vectorFalse_built nodes refs hv hr hd
  rw [refValue_eq input _ _ hb.valid hb.total_valid, hb.total_support]
  exact supportSum_eq_values input nodes refs hv hr hd

/-- Every omission evaluates to the exact sum of all other original operands,
in an arbitrary additive commutative monoid, without cancellation. -/
theorem vectorFalse_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (i : ℕ) (hi : i < refs.length) :
    refValue input (vectorFalse nodes refs).nodes ((vectorFalse nodes refs).one[i]?.getD none) =
      ((refs.eraseIdx i).map (refValue input nodes)).sum := by
  have hb := vectorFalse_built nodes refs hv hr hd
  have hout : i < (vectorFalse nodes refs).one.length := by rw [vectorFalse_length nodes refs]; exact hi
  have hvalid : RefValid (vectorFalse nodes refs).nodes ((vectorFalse nodes refs).one[i]?.getD none) := by
    simp only [List.getElem?_eq_getElem hout, Option.getD_some]
    exact hb.one_valid _ (List.getElem_mem hout)
  rw [refValue_eq input _ _ hb.valid hvalid, vectorFalse_support nodes refs hv hr hd i hi]
  exact supportSum_eq_values input nodes _ hv
    (fun r hh => hr r ((List.eraseIdx_sublist refs i).subset hh))
    (List.Pairwise.sublist (List.eraseIdx_sublist refs i) hd)

/-- Construction preserves every valid pre-existing reference's value. -/
theorem vectorFalse_preserves (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (old : Ref) (ho : RefValid nodes old) :
    refValue input (vectorFalse nodes refs).nodes old = refValue input nodes old := by
  have hb := vectorFalse_built nodes refs hv hr hd
  exact refValue_extends input hb.extension hv hb.valid ho
end Values

end IntegerMultBounds.Networks.PairedVectorCorrect
