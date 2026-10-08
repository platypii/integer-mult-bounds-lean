import IntegerMultBounds.Networks.DisjointBuilder

/-! An executable prefix/suffix leave-one-out builder. A suffix pass shares
all suffix totals; a forward pass shares prefixes and combines each prefix
with the suffix after the omitted position. Counts bound actual new DAG nodes. -/

namespace IntegerMultBounds.Networks.DisjointExclusion

open DisjointCircuit DisjointBuilder
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem refsValid_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    {refs : List Ref} (hr : RefsValid nodes refs) : RefsValid larger refs :=
  fun r h => refValid_extends he (hr r h)

theorem supports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) : supports larger refs = supports nodes refs := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    simp only [supports]
    rw [refSupport_extends he (hr r (by simp)), ih (fun s hs => hr s (by simp [hs]))]

omit [DecidableEq ι] in
theorem map_refSupport_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) :
    refs.map (refSupport larger) = refs.map (refSupport nodes) := by
  apply List.map_congr_left
  exact fun r h => refSupport_extends he (hr r h)

omit [DecidableEq ι] in
theorem disjointRefs_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    DisjointRefs larger refs := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hri := hr _ (List.getElem_mem hi)
  have hrj := hr _ (List.getElem_mem hj)
  rw [refSupport_extends he hri, refSupport_extends he hrj]
  exact List.pairwise_iff_getElem.mp hd i j hi hj hij

theorem disjoint_supports (nodes : List (Node ι)) (s : Finset ι) (refs : List Ref)
    (hd : ∀ r ∈ refs, Disjoint s (refSupport nodes r)) : Disjoint s (supports nodes refs) := by
  induction refs with
  | nil => simp [supports]
  | cons r rs ih =>
    exact Finset.disjoint_union_right.mpr ⟨hd r (by simp), ih (fun x hx => hd x (by simp [hx]))⟩

/-- The support of the suffix strictly after each input position. -/
def afterSupports (nodes : List (Node ι)) : List Ref → List (Finset ι)
  | [] => []
  | _ :: rs => supports nodes rs :: afterSupports nodes rs

theorem afterSupports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) :
    afterSupports larger refs = afterSupports nodes refs := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    have hrs : RefsValid nodes rs := fun s hs => hr s (by simp [hs])
    simp only [afterSupports, supports_extends he rs hrs, ih hrs]

/-- Supports of all leave-one-out queries with a previously accumulated prefix. -/
def omitSupports (nodes : List (Node ι)) (acc : Finset ι) : List Ref → List (Finset ι)
  | [] => []
  | r :: rs => (acc ∪ supports nodes rs) :: omitSupports nodes (acc ∪ refSupport nodes r) rs

theorem omitSupports_extends {nodes larger : List (Node ι)} (he : Extends nodes larger)
    (refs : List Ref) (hr : RefsValid nodes refs) (acc : Finset ι) :
    omitSupports larger acc refs = omitSupports nodes acc refs := by
  induction refs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    have hrs : RefsValid nodes rs := fun s hs => hr s (by simp [hs])
    simp only [omitSupports, supports_extends he rs hrs, refSupport_extends he (hr r (by simp)), ih hrs]

structure SuffixResult (ι : Type*) where
  nodes : List (Node ι)
  total : Ref
  after : List Ref

/-- Build every shared suffix exactly once, using the zero-eliding/interning
constructor for each successive union. -/
def suffixes (nodes : List (Node ι)) : List Ref → SuffixResult ι
  | [] => ⟨nodes, none, []⟩
  | r :: rs =>
    let tail := suffixes nodes rs
    let sum := smartAdd tail.nodes r tail.total
    ⟨sum.1, sum.2, tail.total :: tail.after⟩

structure SuffixBuilt (nodes : List (Node ι)) (refs : List Ref) (result : SuffixResult ι) : Prop where
  built : Built nodes (result.nodes, result.total) (supports nodes refs) refs.length
  after_valid : RefsValid result.nodes result.after
  after_supports : result.after.map (refSupport result.nodes) = afterSupports nodes refs

/-- The suffix pass preserves the original DAG and produces exact valid
suffix references with at most one new node per input position. -/
theorem suffixes_built (nodes : List (Node ι)) (refs : List Ref) (hv : Valid nodes)
    (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    SuffixBuilt nodes refs (suffixes nodes refs) := by
  induction refs with
  | nil => exact ⟨⟨hv, extends_refl _, trivial, rfl, by simp [suffixes]⟩, by simp [suffixes, RefsValid], rfl⟩
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : RefsValid nodes rs := fun s hs => hr s (by simp [hs])
    have hd0 := List.pairwise_cons.mp hd
    have ht := ih hrs hd0.2
    have hds : Disjoint (refSupport (suffixes nodes rs).nodes r)
        (refSupport (suffixes nodes rs).nodes (suffixes nodes rs).total) := by
      rw [refSupport_extends ht.built.extension hr0, ht.built.support_eq]
      exact disjoint_supports nodes _ rs hd0.1
    have ha := smartAdd_built _ r (suffixes nodes rs).total ht.built.valid
      (refValid_extends ht.built.extension hr0) ht.built.refValid hds
    refine ⟨⟨ha.valid, extends_trans ht.built.extension ha.extension, ha.refValid, ?_, ?_⟩, ?_, ?_⟩
    · change refSupport (smartAdd _ r _).1 (smartAdd _ r _).2 = _
      rw [ha.support_eq, refSupport_extends ht.built.extension hr0, ht.built.support_eq]
      rfl
    · have h1 := ht.built.length_le
      have h2 := ha.length_le
      dsimp only at h1 h2
      change (smartAdd _ r _).1.length ≤ nodes.length + (r :: rs).length
      simp only [List.length_cons]
      omega
    · intro s hs
      change s ∈ (suffixes nodes rs).total :: (suffixes nodes rs).after at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact refValid_extends ha.extension ht.built.refValid
      · exact refValid_extends ha.extension (ht.after_valid s hs)
    · change (refSupport (smartAdd _ r _).1 (suffixes nodes rs).total) ::
        ((suffixes nodes rs).after.map (refSupport (smartAdd _ r _).1)) = _
      rw [refSupport_extends ha.extension ht.built.refValid,
        map_refSupport_extends ha.extension _ ht.after_valid, ht.built.support_eq, ht.after_supports]
      rfl

/-- Each forward step creates its leave-one-out sum, then advances the shared
prefix. A mismatched suffix list is unused; the correctness theorem proves
the actual suffix pass supplies exactly one suffix per input. -/
def walk (nodes : List (Node ι)) (acc : Ref) : List Ref → List Ref → List (Node ι) × List Ref
  | [], _ => (nodes, [])
  | _ :: _, [] => (nodes, [])
  | r :: rs, s :: ss =>
    let out := smartAdd nodes acc s
    let next := smartAdd out.1 acc r
    let rest := walk next.1 next.2 rs ss
    (rest.1, out.2 :: rest.2)

structure BatchBuilt (nodes : List (Node ι)) (result : List (Node ι) × List Ref)
    (expected : List (Finset ι)) (budget : ℕ) : Prop where
  valid : Valid result.1
  extension : Extends nodes result.1
  refs_valid : RefsValid result.1 result.2
  supports_eq : result.2.map (refSupport result.1) = expected
  length_le : result.1.length ≤ nodes.length + budget

/-- The forward prefix pass combines disjoint prefix/suffix supports and
constructs all omissions with at most two new nodes per input position. -/
theorem walk_built (nodes : List (Node ι)) (acc : Ref) (refs suffix : List Ref)
    (hv : Valid nodes) (hp : RefValid nodes acc) (hr : RefsValid nodes refs)
    (hs : RefsValid nodes suffix) (hd : DisjointRefs nodes (acc :: refs))
    (he : suffix.map (refSupport nodes) = afterSupports nodes refs) :
    BatchBuilt nodes (walk nodes acc refs suffix)
      (omitSupports nodes (refSupport nodes acc) refs) (2 * refs.length) := by
  induction refs generalizing nodes acc suffix with
  | nil => exact ⟨hv, extends_refl _, by simp [walk, RefsValid], rfl, by simp [walk]⟩
  | cons r rs ih =>
    cases suffix with
    | nil => simp [afterSupports] at he
    | cons s ss =>
      obtain ⟨hss, htail⟩ := List.cons.inj (show refSupport nodes s :: ss.map (refSupport nodes) =
        supports nodes rs :: afterSupports nodes rs from he)
      have hr0 := hr r (by simp)
      have hrs : RefsValid nodes rs := fun x hx => hr x (by simp [hx])
      have hs0 := hs s (by simp)
      have hsss : RefsValid nodes ss := fun x hx => hs x (by simp [hx])
      have hdp := List.pairwise_cons.mp hd
      have hdr := List.pairwise_cons.mp hdp.2
      have hout : Disjoint (refSupport nodes acc) (refSupport nodes s) := by
        rw [hss]
        exact disjoint_supports nodes _ rs (fun x hx => hdp.1 x (by simp [hx]))
      have ho := smartAdd_built nodes acc s hv hp hs0 hout
      have hn := smartAdd_built (smartAdd nodes acc s).1 acc r ho.valid
        (refValid_extends ho.extension hp) (refValid_extends ho.extension hr0) (by
          rw [refSupport_extends ho.extension hp, refSupport_extends ho.extension hr0]
          exact hdp.1 r (by simp))
      have hext := extends_trans ho.extension hn.extension
      have hnew := hn.support_eq
      rw [refSupport_extends ho.extension hp, refSupport_extends ho.extension hr0] at hnew
      have hnewDisjoint : DisjointRefs (smartAdd (smartAdd nodes acc s).1 acc r).1
          ((smartAdd (smartAdd nodes acc s).1 acc r).2 :: rs) := by
        apply List.pairwise_cons.mpr
        refine ⟨?_, disjointRefs_extends hext rs hrs hdr.2⟩
        intro x hx
        rw [hnew, refSupport_extends hext (hrs x hx)]
        exact Finset.disjoint_union_left.mpr ⟨hdp.1 x (by simp [hx]), hdr.1 x hx⟩
      have hi := ih _ _ ss hn.valid hn.refValid (refsValid_extends hext hrs)
        (refsValid_extends hext hsss) hnewDisjoint (by
          rw [map_refSupport_extends hext ss hsss, afterSupports_extends hext rs hrs]
          exact htail)
      refine ⟨hi.valid, extends_trans hext hi.extension, ?_, ?_, ?_⟩
      · intro x hx
        change x ∈ (smartAdd nodes acc s).2 :: (walk _ _ rs ss).2 at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact refValid_extends (extends_trans hn.extension hi.extension) ho.refValid
        · exact hi.refs_valid x hx
      · change refSupport (walk _ _ rs ss).1 (smartAdd nodes acc s).2 ::
          ((walk _ _ rs ss).2.map (refSupport (walk _ _ rs ss).1)) = _
        rw [refSupport_extends (extends_trans hn.extension hi.extension) ho.refValid,
          ho.support_eq, hss, hi.supports_eq, hnew, omitSupports_extends hext rs hrs]
        rfl
      · have h1 := ho.length_le
        have h2 := hn.length_le
        have h3 := hi.length_le
        change (walk _ _ rs ss).1.length ≤ nodes.length + 2 * (r :: rs).length
        simp only [List.length_cons]
        omega

structure Result (ι : Type*) where
  nodes : List (Node ι)
  total : Ref
  one : List Ref

/-- Actual shared-prefix/shared-suffix builder, using `smartAdd` throughout. -/
def leaveOne (nodes : List (Node ι)) (refs : List Ref) : Result ι :=
  let suffix := suffixes nodes refs
  let result := walk suffix.nodes none refs suffix.after
  ⟨result.1, suffix.total, result.2⟩

structure LeaveOneBuilt (nodes : List (Node ι)) (refs : List Ref) (result : Result ι) : Prop where
  valid : Valid result.nodes
  extension : Extends nodes result.nodes
  total_valid : RefValid result.nodes result.total
  total_support : refSupport result.nodes result.total = supports nodes refs
  one_valid : RefsValid result.nodes result.one
  one_supports : result.one.map (refSupport result.nodes) = omitSupports nodes ∅ refs
  length_le : result.nodes.length ≤ nodes.length + 3 * refs.length

/-- The full executable builder constructs the total and every exact omission,
with at most three new DAG nodes per input. Interning can only improve this bound. -/
theorem leaveOne_built (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    LeaveOneBuilt nodes refs (leaveOne nodes refs) := by
  have hs := suffixes_built nodes refs hv hr hd
  have hw := walk_built (suffixes nodes refs).nodes none refs (suffixes nodes refs).after
    hs.built.valid trivial (refsValid_extends hs.built.extension hr) hs.after_valid
    (List.pairwise_cons.mpr ⟨by simp [refSupport], disjointRefs_extends hs.built.extension refs hr hd⟩)
    (by rw [hs.after_supports, afterSupports_extends hs.built.extension refs hr])
  refine ⟨hw.valid, extends_trans hs.built.extension hw.extension,
    refValid_extends hw.extension hs.built.refValid, ?_, hw.refs_valid, ?_, ?_⟩
  · change refSupport (walk _ none refs _).1 (suffixes nodes refs).total = _
    rw [refSupport_extends hw.extension hs.built.refValid, hs.built.support_eq]
  · change (walk _ none refs _).2.map (refSupport (walk _ none refs _).1) = _
    rw [hw.supports_eq, omitSupports_extends hs.built.extension refs hr]
    rfl
  · have h1 := hs.built.length_le
    have h2 := hw.length_le
    dsimp only at h1 h2
    change (walk _ none refs _).1.length ≤ _
    omega

@[simp] theorem omitSupports_length (nodes : List (Node ι)) (acc : Finset ι) (refs : List Ref) :
    (omitSupports nodes acc refs).length = refs.length := by
  induction refs generalizing acc with
  | nil => rfl
  | cons r rs ih => simp [omitSupports, ih]

/-- The support specification is literally the input list with exactly one
position erased, together with any external prefix accumulator. -/
theorem omitSupports_getElem? (nodes : List (Node ι)) (acc : Finset ι)
    (refs : List Ref) (i : ℕ) (hi : i < refs.length) :
    (omitSupports nodes acc refs)[i]? = some (acc ∪ supports nodes (refs.eraseIdx i)) := by
  induction refs generalizing acc i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      simpa only [omitSupports, List.getElem?_cons_succ, List.eraseIdx_cons_succ,
        supports, Finset.union_assoc] using ih (acc ∪ refSupport nodes r) i hi'

theorem leaveOne_length (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    (leaveOne nodes refs).one.length = refs.length := by
  have h := congrArg List.length (leaveOne_built nodes refs hv hr hd).one_supports
  simpa only [List.length_map, omitSupports_length] using h

/-- Every returned output reference has the exact support excluding its
corresponding input position. None references count as genuine empty operands. -/
theorem leaveOne_support (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (i : ℕ) (hi : i < refs.length) :
    refSupport (leaveOne nodes refs).nodes ((leaveOne nodes refs).one[i]?.getD none) =
      supports nodes (refs.eraseIdx i) := by
  have hb := leaveOne_built nodes refs hv hr hd
  have hout : i < (leaveOne nodes refs).one.length := by rw [leaveOne_length nodes refs hv hr hd]; exact hi
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
theorem leaveOne_total_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs) :
    refValue input (leaveOne nodes refs).nodes (leaveOne nodes refs).total =
      (refs.map (refValue input nodes)).sum := by
  have hb := leaveOne_built nodes refs hv hr hd
  rw [refValue_eq input _ _ hb.valid hb.total_valid, hb.total_support]
  exact supportSum_eq_values input nodes refs hv hr hd

/-- Every omission evaluates to the exact sum of all other original operands,
in an arbitrary additive commutative monoid, without cancellation. -/
theorem leaveOne_value (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (i : ℕ) (hi : i < refs.length) :
    refValue input (leaveOne nodes refs).nodes ((leaveOne nodes refs).one[i]?.getD none) =
      ((refs.eraseIdx i).map (refValue input nodes)).sum := by
  have hb := leaveOne_built nodes refs hv hr hd
  have hout : i < (leaveOne nodes refs).one.length := by rw [leaveOne_length nodes refs hv hr hd]; exact hi
  have hvalid : RefValid (leaveOne nodes refs).nodes ((leaveOne nodes refs).one[i]?.getD none) := by
    simp only [List.getElem?_eq_getElem hout, Option.getD_some]
    exact hb.one_valid _ (List.getElem_mem hout)
  rw [refValue_eq input _ _ hb.valid hvalid, leaveOne_support nodes refs hv hr hd i hi]
  exact supportSum_eq_values input nodes _ hv
    (fun r hh => hr r ((List.eraseIdx_sublist refs i).subset hh))
    (List.Pairwise.sublist (List.eraseIdx_sublist refs i) hd)

/-- Construction preserves every valid pre-existing reference's value. -/
theorem leaveOne_preserves (input : ι → A) (nodes : List (Node ι)) (refs : List Ref)
    (hv : Valid nodes) (hr : RefsValid nodes refs) (hd : DisjointRefs nodes refs)
    (old : Ref) (ho : RefValid nodes old) :
    refValue input (leaveOne nodes refs).nodes old = refValue input nodes old := by
  have hb := leaveOne_built nodes refs hv hr hd
  exact refValue_extends input hb.extension hv hb.valid ho
end Values

end IntegerMultBounds.Networks.DisjointExclusion
