import IntegerMultBounds.Networks.PairedStripCorrect

/-! Local correctness of the actual recursive paired-exclusion constructors.
The full recursive block theorem is assembled separately from these contracts. -/

namespace IntegerMultBounds.Networks.PairedCircuitCorrect

open DisjointCircuit DisjointBuilder PairedCircuit

variable {ι : Type*} [DecidableEq ι]

/-- Literal single-output loop, including its real association-table keys. -/
theorem buildSingles_correct (nodes : List (Node ι)) (groups : List (List ℕ))
    (outside : WeightTable) (strips : List Strip) (hv : Valid nodes)
    (hr : ∀ ia ∈ members groups, RefValid nodes (lookup outside ia.1) ∧
      RefValid nodes (stripLookup strips ia.2).total)
    (hd : ∀ ia ∈ members groups, Disjoint (refSupport nodes (lookup outside ia.1))
      (refSupport nodes (stripLookup strips ia.2).total)) :
    let out := buildSingles nodes groups outside strips
    Valid out.1 ∧ Extends nodes out.1 ∧
      List.Forall₂ (fun ia entry => entry.1 = ia.2 ∧
        RefSpec (refSupport nodes (lookup outside ia.1) ∪
          refSupport nodes (stripLookup strips ia.2).total) out.1 entry.2)
        (members groups) out.2 := by
  let Inv := fun ns => Valid ns ∧ Extends nodes ns
  let Post := fun (ia : ℕ × ℕ) ns (entry : ℕ × Ref) => entry.1 = ia.2 ∧
    RefSpec (refSupport nodes (lookup outside ia.1) ∪
      refSupport nodes (stripLookup strips ia.2).total) ns entry.2
  have hb := mapBuild_correct
    (fun ns ia => let r := smartAdd ns (lookup outside ia.1) (stripLookup strips ia.2).total
                 (r.1, (ia.2, r.2))) Inv Post
    (fun _ _ _ _ he hp => ⟨hp.1, refSpec_extends he hp.2⟩)
    nodes (members groups) ⟨hv, extends_refl _⟩ (by
      intro ns hn ia hia
      obtain ⟨hl, hr'⟩ := hr ia hia
      have hsn : refSupport ns (lookup outside ia.1) = refSupport nodes (lookup outside ia.1) :=
        refSupport_extends hn.2 hl
      have hst : refSupport ns (stripLookup strips ia.2).total =
          refSupport nodes (stripLookup strips ia.2).total := refSupport_extends hn.2 hr'
      have hadd := smartAdd_built ns (lookup outside ia.1) (stripLookup strips ia.2).total hn.1
        (refValid_extends hn.2 hl) (refValid_extends hn.2 hr') (by rw [hsn, hst]; exact hd ia hia)
      refine ⟨⟨hadd.valid, extends_trans hn.2 hadd.extension⟩, hadd.extension, rfl,
        hadd.refValid, ?_⟩
      exact hadd.support_eq.trans (by rw [hsn, hst]))
  exact ⟨hb.invariant.1, hb.extension, hb.outputs⟩

/-- Remaining crossing-edge references in the inner pair reconstruction loop. -/
def crossQuery (groups : List (List ℕ)) (edges : EdgeTable) (ij : ℕ × ℕ) (a b : ℕ) : List Ref :=
  crossRefs edges ((groupAt groups ij.1).filter (· != a)) ((groupAt groups ij.2).filter (· != b))

/-- Structural preconditions for one shared-left cross-pair loop, expressed
only using the actual input references and their finite supports. -/
structure CrossLeftReady (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ) : Prop where
  valid : Valid nodes
  far_valid : RefValid nodes (lookup far ij)
  left_valid : RefValid nodes (lookup (stripLookup strips a).outside ij.2)
  left_disjoint : Disjoint (refSupport nodes (lookup far ij))
    (refSupport nodes (lookup (stripLookup strips a).outside ij.2))
  cross_valid : ∀ b ∈ groupAt groups ij.2, RefsValid nodes (crossQuery groups edges ij a b)
  cross_disjoint : ∀ b ∈ groupAt groups ij.2, DisjointRefs nodes (crossQuery groups edges ij a b)
  right_valid : ∀ b ∈ groupAt groups ij.2, RefValid nodes (lookup (stripLookup strips b).outside ij.1)
  right_disjoint : ∀ b ∈ groupAt groups ij.2,
    Disjoint (refSupport nodes (lookup (stripLookup strips b).outside ij.1))
      (supports nodes (crossQuery groups edges ij a b))
  final_disjoint : ∀ b ∈ groupAt groups ij.2,
    Disjoint (refSupport nodes (lookup far ij) ∪ refSupport nodes (lookup (stripLookup strips a).outside ij.2))
      (refSupport nodes (lookup (stripLookup strips b).outside ij.1) ∪
        supports nodes (crossQuery groups edges ij a b))

/-- Support grouping follows the upstream's shared left addition, then the
right-strip/cross addition, then their final addition. -/
def crossPairSupport (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a b : ℕ) : Finset ι :=
  (refSupport nodes (lookup far ij) ∪ refSupport nodes (lookup (stripLookup strips a).outside ij.2)) ∪
    (refSupport nodes (lookup (stripLookup strips b).outside ij.1) ∪ supports nodes (crossQuery groups edges ij a b))

/-- The literal cross loop shares its left partial sum once and proves every
inner result at the final DAG, without replacing the allocation order. -/
theorem buildCrossLeft_correct (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (a : ℕ)
    (h : CrossLeftReady nodes groups edges far strips ij a) :
    let out := buildCrossLeft nodes groups edges far strips ij a
    Valid out.1 ∧ Extends nodes out.1 ∧
      List.Forall₂ (fun b entry => entry.1 = (a,b) ∧
        RefSpec (crossPairSupport nodes groups edges far strips ij a b) out.1 entry.2)
        (groupAt groups ij.2) out.2 := by
  let left := smartAdd nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)
  have hl := smartAdd_built nodes (lookup far ij) (lookup (stripLookup strips a).outside ij.2)
    h.valid h.far_valid h.left_valid h.left_disjoint
  let Inv := fun ns => Valid ns ∧ Extends left.1 ns
  let Post := fun b ns (entry : (ℕ × ℕ) × Ref) => entry.1 = (a,b) ∧
    RefSpec (crossPairSupport nodes groups edges far strips ij a b) ns entry.2
  have hb := mapBuild_correct
    (fun ns b =>
      let cross := DisjointBalanced.total ns (crossQuery groups edges ij a b)
      let right := smartAdd cross.1 (lookup (stripLookup strips b).outside ij.1) cross.2
      let result := smartAdd right.1 left.2 right.2
      (result.1, ((a,b), result.2))) Inv Post
    (fun _ _ _ _ he hp => ⟨hp.1, refSpec_extends he hp.2⟩)
    left.1 (groupAt groups ij.2) ⟨hl.valid, extends_refl _⟩ (by
      intro ns hn b hbg
      have he : Extends nodes ns := extends_trans hl.extension hn.2
      have hc := DisjointBalanced.total_built ns (crossQuery groups edges ij a b) hn.1
        (DisjointExclusion.refsValid_extends he (h.cross_valid b hbg))
        (DisjointExclusion.disjointRefs_extends he _ (h.cross_valid b hbg) (h.cross_disjoint b hbg))
      have hes := DisjointExclusion.supports_extends he _ (h.cross_valid b hbg)
      have hec := extends_trans he hc.extension
      have hcs := hc.support_eq.trans hes
      have hrs := refSupport_extends hec (h.right_valid b hbg)
      have hr := smartAdd_built _ (lookup (stripLookup strips b).outside ij.1) _ hc.valid
        (refValid_extends hec (h.right_valid b hbg)) hc.refValid
        (by rw [hrs, hcs]; exact h.right_disjoint b hbg)
      have her := extends_trans (extends_trans hn.2 hc.extension) hr.extension
      have hls := (refSupport_extends her hl.refValid).trans hl.support_eq
      have hrr := hr.support_eq.trans (by rw [hrs, hcs])
      have hf := smartAdd_built _ left.2 _ hr.valid (refValid_extends her hl.refValid)
        hr.refValid (by rw [hls, hrr]; exact h.final_disjoint b hbg)
      refine ⟨⟨hf.valid, extends_trans her hf.extension⟩,
        extends_trans hc.extension (extends_trans hr.extension hf.extension), rfl,
        hf.refValid, ?_⟩
      exact hf.support_eq.trans (by rw [hls, hrr]; rfl))
  exact ⟨hb.invariant.1, extends_trans hl.extension hb.extension, hb.outputs⟩

/-- The shared-left local preconditions persist through valid DAG extensions. -/
theorem CrossLeftReady.extends {nodes larger : List (Node ι)}
    {groups : List (List ℕ)} {edges far : EdgeTable} {strips : List Strip}
    {ij : ℕ × ℕ} {a : ℕ} (h : CrossLeftReady nodes groups edges far strips ij a)
    (he : Extends nodes larger) (hv : Valid larger) :
    CrossLeftReady larger groups edges far strips ij a := by
  refine ⟨hv, refValid_extends he h.far_valid, refValid_extends he h.left_valid, ?_,
    fun b hb => DisjointExclusion.refsValid_extends he (h.cross_valid b hb),
    fun b hb => DisjointExclusion.disjointRefs_extends he _ (h.cross_valid b hb) (h.cross_disjoint b hb),
    fun b hb => refValid_extends he (h.right_valid b hb), ?_, ?_⟩
  · rw [refSupport_extends he h.far_valid, refSupport_extends he h.left_valid]
    exact h.left_disjoint
  · intro b hb
    rw [refSupport_extends he (h.right_valid b hb),
      DisjointExclusion.supports_extends he _ (h.cross_valid b hb)]
    exact h.right_disjoint b hb
  · intro b hb
    rw [refSupport_extends he h.far_valid, refSupport_extends he h.left_valid,
      refSupport_extends he (h.right_valid b hb),
      DisjointExclusion.supports_extends he _ (h.cross_valid b hb)]
    exact h.final_disjoint b hb

theorem crossPairSupport_extends {nodes larger : List (Node ι)}
    {groups : List (List ℕ)} {edges far : EdgeTable} {strips : List Strip}
    {ij : ℕ × ℕ} {a : ℕ} (h : CrossLeftReady nodes groups edges far strips ij a)
    (he : Extends nodes larger) (b : ℕ) (hb : b ∈ groupAt groups ij.2) :
    crossPairSupport larger groups edges far strips ij a b =
      crossPairSupport nodes groups edges far strips ij a b := by
  unfold crossPairSupport
  rw [refSupport_extends he h.far_valid, refSupport_extends he h.left_valid,
    refSupport_extends he (h.right_valid b hb),
    DisjointExclusion.supports_extends he _ (h.cross_valid b hb)]

omit [DecidableEq ι] in
theorem tableSpec_append {K : Type*} (support : K → Finset ι) (nodes : List (Node ι))
    {left right : List K} {xs ys : List (K × Ref)}
    (hl : TableSpec support left nodes xs) (hr : TableSpec support right nodes ys) :
    TableSpec support (left ++ right) nodes (xs ++ ys) := by
  induction hl with
  | nil => exact hr
  | cons h hs ih => exact .cons h ih

omit [DecidableEq ι] in
/-- Flattening nested constructor loops retains their exact table semantics. -/
theorem tableSpec_flatMap {K J : Type*} (support : J → Finset ι) (keys : K → List J)
    (nodes : List (Node ι)) {inputs : List K} {tables : List (List (J × Ref))}
    (h : List.Forall₂ (fun k table => TableSpec support (keys k) nodes table) inputs tables) :
    TableSpec support (inputs.flatMap keys) nodes tables.flatten := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact tableSpec_append support nodes h ih

/-- Full nested cross-group loop, retaining the exact order of all pairs. -/
theorem buildCrossGroup_correct (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (ij : ℕ × ℕ) (hv : Valid nodes)
    (hr : ∀ a ∈ groupAt groups ij.1, CrossLeftReady nodes groups edges far strips ij a) :
    let out := buildCrossGroup nodes groups edges far strips ij
    Valid out.1 ∧ Extends nodes out.1 ∧
      TableSpec (fun p => crossPairSupport nodes groups edges far strips ij p.1 p.2)
        ((groupAt groups ij.1).flatMap (fun a => (groupAt groups ij.2).map (a, ·))) out.1 out.2 := by
  let Inv := fun ns => Valid ns ∧ Extends nodes ns
  let support := fun p : ℕ × ℕ => crossPairSupport nodes groups edges far strips ij p.1 p.2
  let keys := fun (a : ℕ) => (groupAt groups ij.2).map (a, ·)
  let Post := fun a ns table => TableSpec support (keys a) ns table
  have hb := mapBuild_correct (fun ns a => buildCrossLeft ns groups edges far strips ij a) Inv Post
    (fun a ns larger table he ht => tableSpec_extends support (keys a) he ht)
    nodes (groupAt groups ij.1) ⟨hv, extends_refl _⟩ (by
      intro ns hn a ha
      have hc := buildCrossLeft_correct ns groups edges far strips ij a ((hr a ha).extends hn.2 hn.1)
      refine ⟨⟨hc.1, extends_trans hn.2 hc.2.1⟩, hc.2.1, ?_⟩
      apply List.forall₂_map_left_iff.mpr
      have hout := hc.2.2
      have hs : ∀ b ∈ groupAt groups ij.2,
          crossPairSupport ns groups edges far strips ij a b = support (a,b) :=
        fun b hb => crossPairSupport_extends (hr a ha) hn.2 b hb
      have convert : ∀ (bs : List ℕ) (entries : EdgeTable),
          (∀ b ∈ bs, crossPairSupport ns groups edges far strips ij a b = support (a,b)) →
          List.Forall₂ (fun b entry => entry.1 = (a,b) ∧ RefSpec
            (crossPairSupport ns groups edges far strips ij a b) (buildCrossLeft ns groups edges far strips ij a).1 entry.2) bs entries →
          List.Forall₂ (fun b entry => entry.1 = (a,b) ∧ RefSpec (support (a,b))
            (buildCrossLeft ns groups edges far strips ij a).1 entry.2) bs entries := by
        intro bs entries he hh
        induction hh with
        | nil => exact .nil
        | @cons b entry bs entries hh ht ih =>
          exact .cons ⟨hh.1, (he b (by simp)) ▸ hh.2⟩ (ih (fun b hb => he b (by simp [hb])))
      exact convert _ _ hs hout)
  exact ⟨hb.invariant.1, hb.extension, tableSpec_flatMap support keys _ hb.outputs⟩

omit [DecidableEq ι] in
theorem tableSpec_congr {K : Type*} (support expected : K → Finset ι)
    (nodes : List (Node ι)) {keys : List K} {table : List (K × Ref)}
    (h : TableSpec support keys nodes table) (he : ∀ k ∈ keys, support k = expected k) :
    TableSpec expected keys nodes table := by
  induction h with
  | nil => exact .nil
  | @cons k entry keys table hh ht ih =>
    exact .cons ⟨hh.1, (he k (by simp)) ▸ hh.2⟩ (ih (fun k hk => he k (by simp [hk])))

/-- Exact pair keys emitted by one group-pair block. -/
def crossGroupKeys (groups : List (List ℕ)) (ij : ℕ × ℕ) : List (ℕ × ℕ) :=
  (groupAt groups ij.1).flatMap (fun a => (groupAt groups ij.2).map (a, ·))

/-- All cross-pair loops preserve their real evaluation order while combining
the local support equations into one keyed table contract. -/
theorem buildCrossPairs_correct (nodes : List (Node ι)) (groups : List (List ℕ))
    (edges far : EdgeTable) (strips : List Strip) (expected : ℕ × ℕ → Finset ι)
    (hv : Valid nodes)
    (hr : ∀ ij ∈ pairs (List.range groups.length), ∀ a ∈ groupAt groups ij.1,
      CrossLeftReady nodes groups edges far strips ij a)
    (hs : ∀ ij ∈ pairs (List.range groups.length), ∀ a ∈ groupAt groups ij.1,
      ∀ b ∈ groupAt groups ij.2, crossPairSupport nodes groups edges far strips ij a b = expected (a,b)) :
    let out := buildCrossPairs nodes groups edges far strips
    Valid out.1 ∧ Extends nodes out.1 ∧
      TableSpec expected ((pairs (List.range groups.length)).flatMap (crossGroupKeys groups)) out.1 out.2 := by
  let Inv := fun ns => Valid ns ∧ Extends nodes ns
  let Post := fun ij ns table => TableSpec expected (crossGroupKeys groups ij) ns table
  have hb := mapBuild_correct (fun ns ij => buildCrossGroup ns groups edges far strips ij) Inv Post
    (fun ij ns larger table he ht => tableSpec_extends expected (crossGroupKeys groups ij) he ht)
    nodes (pairs (List.range groups.length)) ⟨hv, extends_refl _⟩ (by
      intro ns hn ij hij
      have hc := buildCrossGroup_correct ns groups edges far strips ij hn.1
        (fun a ha => (hr ij hij a ha).extends hn.2 hn.1)
      refine ⟨⟨hc.1, extends_trans hn.2 hc.2.1⟩, hc.2.1, ?_⟩
      apply tableSpec_congr _ expected _ hc.2.2
      intro p hp
      obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp hp
      subst p
      exact (crossPairSupport_extends (hr ij hij a ha) hn.2 b hb).trans (hs ij hij a ha b hb))
  exact ⟨hb.invariant.1, hb.extension, tableSpec_flatMap expected (crossGroupKeys groups) _ hb.outputs⟩

end IntegerMultBounds.Networks.PairedCircuitCorrect
